/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.NativeFramesPlaneData
public import NativeJordanIdentity

@[expose] public section

set_option backward.privateInPublic true

/-! The cross-plane product has squared scale (1/12) in Appendix
support bound from pairwise unbiasedness. The native Jordan identity supplies commutation of
multiplication by elements of a single frame. -/

noncomputable section

namespace ThirteenPlanes

private theorem nativeJordanIdentity (x y : Glennie.Albert) :
    Glennie.jordan (Glennie.jordan x y) (Glennie.jordan x x) =
      Glennie.jordan x (Glennie.jordan y (Glennie.jordan x x)) := by
  open AlbertSequential NativeAnalysis in
  have h := congrArg recoveredCoordinateEquiv
    (jordan_identity (recoveredCoordinateEquiv.symm x) (recoveredCoordinateEquiv.symm y))
  simpa only [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply] using h

private theorem nativeJordanLinear_commute_square (x : Glennie.Albert) :
    Commute (Glennie.jordanLinear x) (Glennie.jordanLinear (Glennie.jordan x x)) := by
  exact LinearMap.ext fun y => by
    change Glennie.jordan x (Glennie.jordan (Glennie.jordan x x) y) =
      Glennie.jordan (Glennie.jordan x x) (Glennie.jordan x y)
    rw [Glennie.jordan_comm (Glennie.jordan x x) y,
      Glennie.jordan_comm (Glennie.jordan x x) (Glennie.jordan x y)]
    exact (nativeJordanIdentity x y).symm

theorem nativeFrame_point_multiplication_commutes {p : Fin 3 → Glennie.Albert}
    (hp : Glennie.Frame p) (a b : Fin 3) :
    Commute (Glennie.jordanLinear (p a)) (Glennie.jordanLinear (p b)) := by
  by_cases hab : a = b
  · subst b
    exact Commute.refl _
  have hs : Glennie.jordan (p a + (2 : ℝ) • p b) (p a + (2 : ℝ) • p b) =
      p a + (4 : ℝ) • p b := by
    simp only [Glennie.jordan_add_left, Glennie.jordan_add_right, Glennie.jordan_smul_left,
      Glennie.jordan_smul_right, hp.idempotent, hp.orthogonal _ _ hab, hp.orthogonal _ _ (Ne.symm hab),
      smul_zero, add_zero, zero_add, smul_smul]
    norm_num
  have hc := nativeJordanLinear_commute_square (p a + (2 : ℝ) • p b)
  rw [hs] at hc
  let A := Glennie.jordanLinear (p a)
  let B := Glennie.jordanLinear (p b)
  have h : (A + (2 : ℝ) • B) * (A + (4 : ℝ) • B) =
      (A + (4 : ℝ) • B) * (A + (2 : ℝ) • B) := by
    simpa only [map_add, map_smul] using hc.eq
  have hz : (2 : ℝ) • (A * B - B * A) = 0 := by
    calc
      _ = (A + (2 : ℝ) • B) * (A + (4 : ℝ) • B) -
          (A + (4 : ℝ) • B) * (A + (2 : ℝ) • B) := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
        module
      _ = _ := by rw [h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

theorem nativeFrame_multiplication_commutes {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (x x' : nativeFramePlane p) :
    Commute (Glennie.jordanLinear x) (Glennie.jordanLinear x') := by
  obtain ⟨u, hu⟩ := x.property
  obtain ⟨v, hv⟩ := x'.property
  have hxu : (x : Glennie.Albert) = nativeFrameSynthesis p (nativeFrameEntries u) :=
    (congrArg Subtype.val hu).symm.trans (nativeFrameChart_coe hp u)
  have hxv : (x' : Glennie.Albert) = nativeFrameSynthesis p (nativeFrameEntries v) :=
    (congrArg Subtype.val hv).symm.trans (nativeFrameChart_coe hp v)
  rw [hxu, hxv]
  change Commute (Glennie.jordanLinear (∑ a, nativeFrameEntries u a • p a))
    (Glennie.jordanLinear (∑ b, nativeFrameEntries v b • p b))
  simp only [map_sum, map_smul]
  apply Commute.sum_left
  intro a _
  apply Commute.sum_right
  intro b _
  exact ((nativeFrame_point_multiplication_commutes hp a b).smul_left _).smul_right _

private theorem nativeJordan_cross_is_trace_zero (c : TightNativeCode) {f g : Fin 13}
    (hfg : f ≠ g) (x : c.decomposition.plane f) (y : c.decomposition.plane g) :
    Glennie.traceless (Glennie.jordan x y) = Glennie.jordan x y := by
  have h : Glennie.trace (Glennie.jordan x y) = 0 :=
    (c.planes_orthogonal hfg).inner_eq x.property y.property
  simp [Glennie.traceless, h]

private theorem nativeCrossProduct_inner_swapped (c : TightNativeCode) {f g : Fin 13}
    (hfg : f ≠ g) (x x' : c.decomposition.plane f) (y y' : c.decomposition.plane g) :
    inner ℝ (nativeCenteredJordan x y) (nativeCenteredJordan x' y') =
      inner ℝ (nativeCenteredJordan x y') (nativeCenteredJordan x' y) := by
  change Glennie.inner (Glennie.traceless (Glennie.jordan x y))
      (Glennie.traceless (Glennie.jordan x' y')) =
    Glennie.inner (Glennie.traceless (Glennie.jordan x y'))
      (Glennie.traceless (Glennie.jordan x' y))
  rw [nativeJordan_cross_is_trace_zero c hfg x y, nativeJordan_cross_is_trace_zero c hfg x' y',
    nativeJordan_cross_is_trace_zero c hfg x y', nativeJordan_cross_is_trace_zero c hfg x' y]
  have hc := LinearMap.congr_fun (nativeFrame_multiplication_commutes (c.frame f) x x').eq
    (y' : Glennie.Albert)
  simp only [mul_apply_eq_comp, Glennie.jordanLinear_apply] at hc
  calc
    _ = Glennie.inner y (Glennie.jordan x (Glennie.jordan x' y')) := by
      rw [← Glennie.inner_jordan_associative (y : Glennie.Albert) x,
        Glennie.jordan_comm (y : Glennie.Albert) x]
    _ = Glennie.inner y (Glennie.jordan x' (Glennie.jordan x y')) :=
      congrArg (Glennie.inner y) hc
    _ = Glennie.inner (Glennie.jordan x' y) (Glennie.jordan x y') := by
      rw [← Glennie.inner_jordan_associative (y : Glennie.Albert) x',
        Glennie.jordan_comm (y : Glennie.Albert) x']
    _ = _ := Glennie.inner_comm _ _

/-- Inner products of products from two distinct frame planes. This is the
scaled isometry identity on pure tensors in Appendix support bound from pairwise unbiasedness. -/
theorem TightNativeCode.crossProduct_inner (c : TightNativeCode) {f g : Fin 13}
    (hfg : f ≠ g) (x x' : c.decomposition.plane f) (y y' : c.decomposition.plane g) :
    inner ℝ (nativeCenteredJordan x y) (nativeCenteredJordan x' y') =
      inner ℝ (x : NativeTraceless) x' * inner ℝ (y : NativeTraceless) y' / 12 := by
  have h := nativeEqualCubic_squareLaw.polarized
    (x : NativeTraceless) x' (y : NativeTraceless) y'
  change inner ℝ (nativeCenteredJordan x x') (nativeCenteredJordan y y') +
      inner ℝ (nativeCenteredJordan x y) (nativeCenteredJordan x' y') +
      inner ℝ (nativeCenteredJordan x y') (nativeCenteredJordan x' y) =
    (inner ℝ (x : NativeTraceless) x' * inner ℝ (y : NativeTraceless) y' +
      inner ℝ (x : NativeTraceless) y * inner ℝ (x' : NativeTraceless) y' +
      inner ℝ (x : NativeTraceless) y' * inner ℝ (x' : NativeTraceless) y) / 6 at h
  rw [← nativeCrossProduct_inner_swapped c hfg x x' y y'] at h
  simp only [(c.planes_orthogonal hfg).inner_eq
      (nativeFramePlane_closed (c.frame f) x.property x'.property)
      (nativeFramePlane_closed (c.frame g) y.property y'.property),
    (c.planes_orthogonal hfg).inner_eq x.property y.property,
    (c.planes_orthogonal hfg).inner_eq x.property y'.property,
    zero_add, zero_mul, add_zero] at h
  linarith

end ThirteenPlanes
