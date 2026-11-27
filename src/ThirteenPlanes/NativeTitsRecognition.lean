module

public import ThirteenPlanes.NativeTits

@[expose] public section

set_option backward.privateInPublic true

open scoped RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

private theorem nativeTraceless_compact_range :
    Glennie.traceLinear.ker.map nativeCompactTitsEquiv.toLinearMap =
      Tits.compactTitsTracelessSubspace := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Tits.CompactTits.trace (nativeCompactTitsEquiv x) = 0
    rw [nativeCompactTitsEquiv_trace]
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := nativeCompactTitsEquiv.surjective y
    refine ⟨x, ?_, rfl⟩
    change Tits.CompactTits.trace (nativeCompactTitsEquiv x) = 0 at hy
    rw [nativeCompactTitsEquiv_trace] at hy
    exact hy

def nativeTracelessCompactEquiv : NativeTraceless ≃ₗᵢ[ℝ] Tits.CompactTitsTraceless :=
  (nativeCompactTitsEquiv.submoduleMap Glennie.traceLinear.ker).trans
    (LinearIsometryEquiv.ofEq _ _ nativeTraceless_compact_range)

@[simp] theorem nativeTracelessCompactEquiv_val (x : NativeTraceless) :
    (nativeTracelessCompactEquiv x).val = nativeCompactTitsEquiv x.val := rfl

private theorem nativeTracelessCompactEquiv_product (x y : NativeTraceless) :
    nativeTracelessCompactEquiv (nativeCenteredJordan x y) =
      Tits.CompactTits.center
        (Tits.CompactTits.product (nativeTracelessCompactEquiv x).val (nativeTracelessCompactEquiv y).val) := by
  apply Subtype.ext
  simp only [nativeTracelessCompactEquiv_val, nativeCenteredJordan_apply]
  change nativeCompactTitsEquiv (Glennie.traceless (Glennie.jordan x.val y.val)) =
    Tits.CompactTits.product (nativeCompactTitsEquiv x.val) (nativeCompactTitsEquiv y.val) -
    (Tits.CompactTits.trace (Tits.CompactTits.product (nativeCompactTitsEquiv x.val)
      (nativeCompactTitsEquiv y.val)) / 3) • Tits.CompactTits.one
  rw [← nativeCompactTitsEquiv_product, nativeCompactTitsEquiv_trace]
  simp only [Glennie.traceless, map_sub, map_smul, nativeCompactTitsEquiv_one]

/-- Unmarked identification of the signed trace-free fields with the native octonionic fields. -/
def signedNativeEquiv : SignedField ≃ₗᵢ[ℝ] NativeTraceless :=
  gradedTitsEquiv.trans nativeTracelessCompactEquiv.symm

@[simp] theorem nativeTracelessCompactEquiv_signedNativeEquiv (x : SignedField) :
    nativeTracelessCompactEquiv (signedNativeEquiv x) = gradedTitsEquiv x :=
  nativeTracelessCompactEquiv.apply_symm_apply _

theorem signedNativeEquiv_product (x y : SignedField) :
    signedNativeEquiv (signedEqualCubic.L x y) =
      nativeEqualCubic.L (signedNativeEquiv x) (signedNativeEquiv y) := by
  apply nativeTracelessCompactEquiv.injective
  simp only [nativeEqualCubic, SymmetricCubic.L_ofProduct,
    nativeTracelessCompactEquiv_signedNativeEquiv, gradedTitsEquiv_signedProduct,
    nativeTracelessCompactEquiv_product]

/-- The full-strength signed trilinear tensor is the actual native Albert trace tensor. -/
theorem signedEqualCubic_eq_native (x y z : SignedField) :
    signedEqualCubic.apply x y z =
      nativeEqualCubic.apply (signedNativeEquiv x) (signedNativeEquiv y) (signedNativeEquiv z) := by
  change ⟪signedEqualCubic.L x y, z⟫ =
    ⟪nativeEqualCubic.L (signedNativeEquiv x) (signedNativeEquiv y), signedNativeEquiv z⟫
  rw [← signedNativeEquiv_product]
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← signedNativeEquiv.map_add, signedNativeEquiv.norm_map]

end

end ThirteenPlanes
