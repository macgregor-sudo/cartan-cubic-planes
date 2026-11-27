/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.Contracts
public import Glennie.Hilbert
public import NativeNewtonCubic

@[expose] public section

set_option backward.privateInPublic true

/-! The traceless part of the compact Albert algebra with its raw trace metric.

The carrier, trace metric, and characteristic identity are from
`albert-sequential-measurements` v2.0.0 at commit
10e5ca8ce341a1cb3a812569d3081005a40007c8
(`Glennie/Hilbert.lean`, `NativeRecoveredCoordinates.lean`, and
`NativeNewtonCubic.lean`). -/

noncomputable section

namespace ThirteenPlanes

abbrev NativeTraceless := ↥Glennie.traceLinear.ker

@[simp] theorem nativeTraceless_trace (x : NativeTraceless) :
    Glennie.trace (x : Glennie.Albert) = 0 := x.property

theorem nativeTraceless_finrank : Module.finrank ℝ NativeTraceless = 26 := by
  have hsurj : Function.Surjective Glennie.traceLinear := by
    intro r
    refine ⟨(r / 3) • (1 : Glennie.Albert), ?_⟩
    simp
  have h := Glennie.traceLinear.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Glennie.albert_finrank] at h
  change 1 + Module.finrank ℝ NativeTraceless = 27 at h
  omega

def nativeCenter : Glennie.Albert →ₗ[ℝ] NativeTraceless where
  toFun x := ⟨Glennie.traceless x, Glennie.trace_traceless x⟩
  map_add' x y := by
    apply Subtype.ext
    change Glennie.traceless (x + y) = Glennie.traceless x + Glennie.traceless y
    simp only [Glennie.traceless, Glennie.trace_add, add_div, add_smul]
    abel
  map_smul' r x := by
    apply Subtype.ext
    change Glennie.traceless (r • x) = r • Glennie.traceless x
    simp only [Glennie.traceless, Glennie.trace_smul, mul_div_assoc, mul_smul, smul_sub]

@[simp] theorem nativeCenter_coe (x : Glennie.Albert) :
    (nativeCenter x : Glennie.Albert) = Glennie.traceless x := rfl

@[simp] theorem nativeCenter_of_trace_zero (x : NativeTraceless) : nativeCenter x = x := by
  apply Subtype.ext
  simp [Glennie.traceless]

theorem nativeInner_one_left (x : Glennie.Albert) : Glennie.inner 1 x = Glennie.trace x := by
  simp [Glennie.inner]

theorem nativeInner_one_right (x : Glennie.Albert) : Glennie.inner x 1 = Glennie.trace x := by
  simp [Glennie.inner]

theorem nativeInner_center_left (y : Glennie.Albert) (z : NativeTraceless) :
    Glennie.inner (Glennie.traceless y) z = Glennie.inner y z := by
  rw [Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_smul_left, nativeInner_one_left,
    nativeTraceless_trace, mul_zero, sub_zero]

def nativeCenteredJordan : NativeTraceless →ₗ[ℝ] NativeTraceless →ₗ[ℝ] NativeTraceless :=
  LinearMap.mk₂ ℝ (fun x y => nativeCenter (Glennie.jordan x y))
    (by intros; simp only [Submodule.coe_add, Glennie.jordan_add_left, map_add])
    (by intros; simp only [Submodule.coe_smul, Glennie.jordan_smul_left, map_smul])
    (by intros; simp only [Submodule.coe_add, Glennie.jordan_add_right, map_add])
    (by intros; simp only [Submodule.coe_smul, Glennie.jordan_smul_right, map_smul])

@[simp] theorem nativeCenteredJordan_apply (x y : NativeTraceless) :
    nativeCenteredJordan x y = nativeCenter (Glennie.jordan x y) := rfl

theorem nativeCenterJordan_comm (x y : NativeTraceless) :
    nativeCenteredJordan x y = nativeCenteredJordan y x := by
  simp only [nativeCenteredJordan_apply, Glennie.jordan_comm]

theorem nativeCenterJordan_inner_swap (x y z : NativeTraceless) :
    inner ℝ (nativeCenteredJordan x y) z = inner ℝ (nativeCenteredJordan x z) y := by
  change Glennie.inner (Glennie.traceless (Glennie.jordan x y)) z =
    Glennie.inner (Glennie.traceless (Glennie.jordan x z)) y
  rw [nativeInner_center_left, nativeInner_center_left,
    Glennie.inner_jordan_associative, Glennie.inner_jordan_associative,
    Glennie.jordan_comm (y : Glennie.Albert) z]

def nativeEqualCubic : SymmetricCubic NativeTraceless :=
  SymmetricCubic.ofProduct nativeCenteredJordan nativeCenterJordan_comm nativeCenterJordan_inner_swap

@[simp] theorem nativeEqualCubic_square (x : NativeTraceless) :
    nativeEqualCubic.squareMap x = nativeCenter (Glennie.jordan x x) := rfl

private theorem nativeCube_of_trace_zero (x : Glennie.Albert) (hx : Glennie.trace x = 0) :
    Glennie.jordan x (Glennie.jordan x x) =
      (Glennie.trace (Glennie.jordan x x) / 2) • x +
      (Glennie.trace (Glennie.jordan x (Glennie.jordan x x)) / 3) • (1 : Glennie.Albert) := by
  open AlbertSequential NativeAnalysis in
  have h := congrArg recoveredCoordinateEquiv
    (cubic_characteristic_identity (recoveredCoordinateEquiv.symm x))
  simp only [map_add, map_sub, map_smul, ← recoveredCoordinateEquiv_trace,
    recoveredCoordinateEquiv_jordanMul, recoveredCoordinateEquiv_unit,
    LinearEquiv.apply_symm_apply, hx] at h
  calc
    _ = _ := h
    _ = _ := by
      simp only [zero_pow (show (2 : ℕ) ≠ 0 by decide), zero_pow (show (3 : ℕ) ≠ 0 by decide),
        zero_smul, zero_sub]
      module

theorem nativeCenteredSquare_norm_sq (x : NativeTraceless) :
    ‖nativeCenter (Glennie.jordan x x)‖ ^ 2 = ‖x‖ ^ 4 / 6 := by
  let X : Glennie.Albert := x
  let S := Glennie.jordan X X
  have hx : Glennie.trace X = 0 := x.property
  have hXS : Glennie.inner X X = Glennie.trace S := rfl
  have hSS : Glennie.inner S S = (Glennie.trace S) ^ 2 / 2 := by
    change Glennie.inner (Glennie.jordan X X) S = _
    rw [Glennie.inner_jordan_associative, nativeCube_of_trace_zero X hx,
      Glennie.inner_add_right, Glennie.inner_smul_right, Glennie.inner_smul_right,
      nativeInner_one_right, hx, mul_zero, add_zero, hXS]
    change Glennie.trace S / 2 * Glennie.trace S = _
    ring
  have hc : Glennie.inner (Glennie.traceless S) (Glennie.traceless S) =
      (Glennie.trace S) ^ 2 / 6 := by
    rw [Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_sub_right, Glennie.inner_sub_right,
      Glennie.inner_smul_left, Glennie.inner_smul_left, Glennie.inner_smul_right,
      Glennie.inner_smul_right, nativeInner_one_left, nativeInner_one_right,
      nativeInner_one_right, Glennie.trace_unit, hSS]
    ring
  have hnorm : ‖x‖ ^ 2 = Glennie.trace S := by
    rw [← real_inner_self_eq_norm_sq]
    exact hXS
  rw [← real_inner_self_eq_norm_sq]
  change Glennie.inner (Glennie.traceless S) (Glennie.traceless S) = _
  rw [hc, ← hnorm]
  ring

theorem nativeEqualCubic_squareLaw : HasSquareLaw nativeEqualCubic := by
  intro x
  exact nativeCenteredSquare_norm_sq x

end ThirteenPlanes
