/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FrameSupportCounting

@[expose] public section

set_option backward.privateInPublic true

/-! Nonzero weight detects a nonzero trilinear restriction on the actual frame planes. -/

noncomputable section

namespace ThirteenPlanes

private theorem frameVector_expansion (c : TightNativeCode) (f : Fin 13)
    (x : c.decomposition.plane f) :
    (x : NativeTraceless) = ∑ i : Fin 2,
      ((c.frameBasis f).toBasis.repr x i) • c.frameVector f i := by
  have h := congrArg (fun y : c.decomposition.plane f => (y : NativeTraceless))
    ((c.frameBasis f).toBasis.sum_repr x)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, TightNativeCode.frameVector,
    OrthonormalBasis.coe_toBasis] using h.symm

theorem TightNativeCode.frameWeight_eq_zero_iff (c : TightNativeCode) (f g h : Fin 13) :
    c.frameWeight f g h = 0 ↔ ∀ (x : c.decomposition.plane f)
      (y : c.decomposition.plane g) (z : c.decomposition.plane h),
        nativeEqualCubic.apply x y z = 0 := by
  let coefficient (i j k : Fin 2) :=
    nativeEqualCubic.apply (c.frameVector f i) (c.frameVector g j) (c.frameVector h k)
  have hw : c.frameWeight f g h = 6 * ∑ k, ∑ i, ∑ j, (coefficient i j k) ^ 2 :=
    c.frameWeight_eq_cubic f g h
  constructor
  · intro hz x y z
    rw [hw] at hz
    have hsum : ∑ k, ∑ i, ∑ j, (coefficient i j k)^2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (by norm_num)
    have hc (i j k : Fin 2) : coefficient i j k = 0 := by
      have hk : ∑ i, ∑ j, (coefficient i j k)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
          Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => sq_nonneg _)).mp
          hsum k (Finset.mem_univ k)
      have hi : ∑ j, (coefficient i j k)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
          Finset.sum_nonneg fun m _ => sq_nonneg _)).mp hk i (Finset.mem_univ i)
      have hj : (coefficient i j k)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg _)).mp hi j (Finset.mem_univ j)
      exact sq_eq_zero_iff.mp hj
    change nativeEqualCubic.trilinear (x : NativeTraceless) y z = 0
    rw [frameVector_expansion c f x, frameVector_expansion c g y, frameVector_expansion c h z]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      SymmetricCubic.trilinear_apply, show ∀ i j k, nativeEqualCubic.apply (c.frameVector f i)
        (c.frameVector g j) (c.frameVector h k) = 0 from hc, smul_zero, Finset.sum_const_zero]
  · intro hn
    have hc (i j k : Fin 2) : coefficient i j k = 0 :=
      hn (c.frameBasis f i) (c.frameBasis g j) (c.frameBasis h k)
    simp only [hw, hc, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero]

theorem TightNativeCode.mem_support_iff (c : TightNativeCode) (t : NativeFrameTriple) :
    t ∈ c.tripleSupport ↔
      ¬ ∀ (x : c.decomposition.plane t.val.1)
        (y : c.decomposition.plane t.val.2.1) (z : c.decomposition.plane t.val.2.2),
        nativeEqualCubic.apply x y z = 0 := by
  change t ∈ Finset.univ.filter (fun u : NativeFrameTriple =>
    c.frameWeight u.val.1 u.val.2.1 u.val.2.2 ≠ 0) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_congr (c.frameWeight_eq_zero_iff _ _ _)

end ThirteenPlanes
