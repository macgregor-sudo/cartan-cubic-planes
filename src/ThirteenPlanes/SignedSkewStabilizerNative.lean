module

public import ThirteenPlanes.SignedSkewStabilizerCore
public import ThirteenPlanes.NativeTitsRecognition
public import NativeRecoveredCoordinates

@[expose] public section

set_option backward.privateInPublic true

open scoped RealInnerProductSpace

namespace ThirteenPlanes.SignedSkew

noncomputable section

attribute [local irreducible] signedNativeEquiv signedEqualCubic

private def signedToNativeTraceFree : SignedField →ₗ[ℝ] Glennie.Albert :=
  Glennie.traceLinear.ker.subtype.comp signedNativeEquiv.toLinearMap

private def nativeToSignedTraceFree : Glennie.Albert →ₗ[ℝ] SignedField :=
  signedNativeEquiv.symm.toLinearMap.comp nativeCenter

@[simp] private theorem signedToNativeTraceFree_trace (x : SignedField) :
    Glennie.trace (signedToNativeTraceFree x) = 0 := (signedNativeEquiv x).property

@[simp] private theorem nativeCenter_one : nativeCenter (1 : Glennie.Albert) = 0 := by
  apply Subtype.ext
  change Glennie.traceless (1 : Glennie.Albert) = 0
  simp [Glennie.traceless]

@[simp] private theorem nativeToSignedTraceFree_signedToNativeTraceFree (x : SignedField) :
    nativeToSignedTraceFree (signedToNativeTraceFree x) = x := by
  change signedNativeEquiv.symm (nativeCenter (signedNativeEquiv x).val) = x
  rw [nativeCenter_of_trace_zero, LinearIsometryEquiv.symm_apply_apply]

@[simp] private theorem nativeToSignedTraceFree_one : nativeToSignedTraceFree (1 : Glennie.Albert) = 0 := by
  change signedNativeEquiv.symm (nativeCenter 1) = 0
  rw [nativeCenter_one, map_zero]

private theorem native_join_trace (x : Glennie.Albert) :
    signedToNativeTraceFree (nativeToSignedTraceFree x) +
      (Glennie.trace x / 3) • (1 : Glennie.Albert) = x := by
  change (signedNativeEquiv (signedNativeEquiv.symm (nativeCenter x))).val + _ = _
  rw [LinearIsometryEquiv.apply_symm_apply, nativeCenter_coe, Glennie.traceless, sub_add_cancel]

private def signedSplitNativeEquiv : SignedWithUnit ≃ₗ[ℝ] Glennie.Albert where
  toFun u := signedToNativeTraceFree u.1 + u.2 • (1 : Glennie.Albert)
  invFun x := (nativeToSignedTraceFree x, Glennie.trace x / 3)
  left_inv u := by
    apply Prod.ext
    · change nativeToSignedTraceFree (signedToNativeTraceFree u.1 + u.2 • (1 : Glennie.Albert)) = u.1
      simp
    · change Glennie.trace (signedToNativeTraceFree u.1 + u.2 • (1 : Glennie.Albert)) / 3 = u.2
      simp
  right_inv := native_join_trace
  map_add' u v := by
    change signedToNativeTraceFree (u.1+v.1) + (u.2+v.2) • (1 : Glennie.Albert) = _
    simp only [map_add, add_smul]
    abel
  map_smul' r u := by
    change signedToNativeTraceFree (r • u.1) + (r*u.2) • (1 : Glennie.Albert) = _
    simp only [map_smul, smul_add, smul_smul, RingHom.id_apply]

private theorem signedToNativeTraceFree_jordan (x y : SignedField) :
    Glennie.jordan (signedToNativeTraceFree x) (signedToNativeTraceFree y) =
      signedToNativeTraceFree (signedEqualCubic.L x y) + (⟪x,y⟫ / 3 : ℝ) • (1 : Glennie.Albert) := by
  have hp := signedNativeEquiv_product x y
  simp only [nativeEqualCubic, SymmetricCubic.L_ofProduct, nativeCenteredJordan_apply] at hp
  have hre : signedToNativeTraceFree (signedEqualCubic.L x y) =
      Glennie.traceless (Glennie.jordan (signedToNativeTraceFree x) (signedToNativeTraceFree y)) :=
    congrArg Subtype.val hp
  have ht : Glennie.trace (Glennie.jordan (signedToNativeTraceFree x) (signedToNativeTraceFree y)) =
      ⟪x,y⟫ := by
    rw [← Glennie.inner, ← Glennie.hilbert_inner_eq_native]
    change ⟪signedNativeEquiv x,signedNativeEquiv y⟫ = _
    exact signedNativeEquiv.inner_map_map x y
  rw [hre, ← ht, Glennie.traceless, sub_add_cancel]

private theorem signedSplitNativeEquiv_product (x y : SignedWithUnit) :
    signedSplitNativeEquiv (signedSplitProduct x y) =
      Glennie.jordan (signedSplitNativeEquiv x) (signedSplitNativeEquiv y) := by
  change signedToNativeTraceFree (signedEqualCubic.L x.1 y.1 + x.2 • y.1 + y.2 • x.1) +
    (⟪x.1,y.1⟫ / 3 + x.2*y.2) • (1 : Glennie.Albert) =
      Glennie.jordan (signedToNativeTraceFree x.1 + x.2 • (1 : Glennie.Albert))
        (signedToNativeTraceFree y.1 + y.2 • (1 : Glennie.Albert))
  simp only [map_add, map_smul, add_smul, Glennie.jordan_add_left, Glennie.jordan_add_right,
    Glennie.jordan_smul_left, Glennie.jordan_smul_right, signedToNativeTraceFree_jordan]
  simp
  rw [smul_smul, mul_comm y.2 x.2]
  abel

def signedSplitSequentialEquiv : SignedWithUnit ≃ₗ[ℝ] AlbertSequential.Albert :=
  signedSplitNativeEquiv.trans AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv.symm

private theorem recovered_signedSplit_native (x : SignedWithUnit) :
    AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv (signedSplitSequentialEquiv x) =
      signedSplitNativeEquiv x :=
  AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv.apply_symm_apply _

theorem signedSplitSequentialEquiv_product (x y : SignedWithUnit) :
    signedSplitSequentialEquiv (signedSplitProduct x y) =
      AlbertSequential.jordanMul (signedSplitSequentialEquiv x) (signedSplitSequentialEquiv y) := by
  apply AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv.injective
  rw [AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_jordanMul, recovered_signedSplit_native,
    recovered_signedSplit_native, recovered_signedSplit_native]
  exact signedSplitNativeEquiv_product x y

theorem signedSplitSequentialEquiv_unit :
    signedSplitSequentialEquiv (0,1) = AlbertSequential.albertUnit := by
  apply AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv.injective
  rw [AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_unit, recovered_signedSplit_native]
  change signedToNativeTraceFree 0 + (1 : ℝ) • (1 : Glennie.Albert) = _
  simp

theorem signedSplitSequentialEquiv_trace (u : SignedWithUnit) :
    AlbertSequential.albertTrace (signedSplitSequentialEquiv u) = 3 * u.2 := by
  rw [← AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_trace, recovered_signedSplit_native]
  change Glennie.trace (signedToNativeTraceFree u.1 + u.2 • (1 : Glennie.Albert)) = _
  simp [mul_comm]

end

end ThirteenPlanes.SignedSkew
