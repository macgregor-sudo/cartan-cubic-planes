module

public import ThirteenPlanes.AlbertGrading.Completion.PairFrame

@[expose] public section

/-! The pair criterion in the native Albert algebra.

Orthonormal traceless `x,y` with `x² + y² = (2/3)e` satisfy `⟨x²,y²⟩ = ⟨x∘y,x∘y⟩ = 1/6`, by the
round quartic `⟨z²,z²⟩ = ½⟨z,z⟩²` at `z = x ± y` (manuscript eq. 4-equal-O). After an actual
automorphism diagonalizes `x`, `PairFrame` gives a frame whose span contains `x` and `y`. -/

namespace ThirteenPlanes.AlbertGrading.CompletionO

open Glennie
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- The round quartic of a traceless Albert element, from the square law. -/
theorem traceless_quartic (Z : Albert) (hZ : trace Z = 0) :
    inner (jordan Z Z) (jordan Z Z) = (inner Z Z) ^ 2 / 2 := by
  let z : NativeTraceless := ⟨Z, hZ⟩
  have h := nativeCenteredSquare_norm_sq z
  have e1 : ‖nativeCenter (jordan (z : Albert) (z : Albert))‖ = ‖traceless (jordan Z Z)‖ := by
    rfl
  have e2 : ‖z‖ = ‖Z‖ := rfl
  rw [e1, e2, show ‖Z‖ ^ 4 = (‖Z‖ ^ 2) ^ 2 by ring, native_norm_sq, native_norm_sq] at h
  have ht : trace (jordan Z Z) = inner Z Z := rfl
  rw [traceless, Glennie.inner_sub_left, Glennie.inner_sub_right, Glennie.inner_sub_right,
    Glennie.inner_smul_left, Glennie.inner_smul_left, Glennie.inner_smul_right,
    Glennie.inner_smul_right, nativeInner_one_left,
    nativeInner_one_right, nativeInner_one_right, trace_unit, ht] at h
  nlinarith [h]

/-- The pair criterion forces equality of `⟨x²,y²⟩` and `|x∘y|²`. -/
theorem pair_gap (X Y : Albert) (htx : trace X = 0) (hty : trace Y = 0)
    (hxx : inner X X = 1) (hyy : inner Y Y = 1) (hxy : inner X Y = 0)
    (hsq : jordan X X + jordan Y Y = (2 / 3 : ℝ) • (1 : Albert)) :
    inner (jordan X X) (jordan Y Y) = inner (jordan X Y) (jordan X Y) := by
  have hyx : inner Y X = 0 := by rw [inner_comm]; exact hxy
  have hp : jordan (X + Y) (X + Y) = jordan X X + jordan Y Y + (2 : ℝ) • jordan X Y := by
    rw [jordan_add_left, jordan_add_right, jordan_add_right, jordan_comm Y X]
    module
  have hm : jordan (X - Y) (X - Y) = jordan X X + jordan Y Y - (2 : ℝ) • jordan X Y := by
    rw [jordan_sub_left, jordan_sub_right, jordan_sub_right, jordan_comm Y X]
    module
  have qp := traceless_quartic (X + Y) (by rw [trace_add, htx, hty, add_zero])
  have qm := traceless_quartic (X - Y) (by rw [trace_sub, htx, hty, sub_zero])
  have qx := traceless_quartic X htx
  have qy := traceless_quartic Y hty
  have npp : inner (X + Y) (X + Y) = 2 := by
    rw [inner_add_left, inner_add_right, inner_add_right, hxx, hyy, hxy, hyx]; norm_num
  have nmm : inner (X - Y) (X - Y) = 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hxx, hyy, hxy, hyx]; norm_num
  rw [hp, hsq, npp] at qp
  rw [hm, hsq, nmm] at qm
  rw [hxx] at qx
  rw [hyy] at qy
  have hAA : inner ((2 / 3 : ℝ) • (1 : Albert)) ((2 / 3 : ℝ) • (1 : Albert)) = 4 / 3 := by
    rw [inner_smul_left, inner_smul_right, nativeInner_one_left, trace_unit]; norm_num
  have hA : inner (jordan X X + jordan Y Y) (jordan X X + jordan Y Y) =
      inner ((2 / 3 : ℝ) • (1 : Albert)) ((2 / 3 : ℝ) • (1 : Albert)) := by rw [hsq]
  rw [hAA, inner_add_left, inner_add_right, inner_add_right, qx, qy,
    inner_comm (jordan Y Y) (jordan X X)] at hA
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right] at qp qm
  have h11 : inner (1 : Albert) 1 = 3 := by rw [nativeInner_one_left, trace_unit]
  linarith

/-- Two orthonormal traceless Albert elements with `x² + y² = (2/3)e` lie in the span of one actual
frame. -/
theorem pair_common_frame (x y : Albert) (htx : trace x = 0) (hty : trace y = 0)
    (hxx : inner x x = 1) (hyy : inner y y = 1) (hxy : inner x y = 0)
    (hsq : jordan x x + jordan y y = (2 / 3 : ℝ) • (1 : Albert)) :
    ∃ q : Fin 3 → Albert, Frame q ∧
      ∃ l m : Fin 3 → ℝ, x = ∑ b, l b • q b ∧ y = ∑ b, m b • q b := by
  have hgap := pair_gap x y htx hty hxx hyy hxy hsq
  obtain ⟨g, hg⟩ := native_diagonalization x
  have hsqg : jordan (g.equiv x) (g.equiv x) + jordan (g.equiv y) (g.equiv y) =
      (2 / 3 : ℝ) • (1 : Albert) := by
    rw [← g.map_jordan, ← g.map_jordan, ← map_add, hsq, map_smul, g.map_unit]
  have hgapg : inner (jordan (g.equiv x) (g.equiv x)) (jordan (g.equiv y) (g.equiv y)) =
      inner (jordan (g.equiv x) (g.equiv y)) (jordan (g.equiv x) (g.equiv y)) := by
    rw [← g.map_jordan, ← g.map_jordan, ← g.map_jordan, g.inner_map, g.inner_map]
    exact hgap
  obtain ⟨Q, hQ, l, m, hl, hm⟩ := diag_common_frame (g.equiv x) (g.equiv y) hg
    (by rw [g.map_trace]; exact htx) (by rw [g.inner_map]; exact hxx)
    (by rw [g.map_trace]; exact hty) hsqg hgapg
  refine ⟨fun b => g.symm.equiv (Q b), g.symm.map_frame Q hQ, l, m, ?_, ?_⟩
  · have h := congrArg g.equiv.symm hl
    simpa only [LinearEquiv.symm_apply_apply, map_sum, map_smul,
      CompactAutomorphism.symm_apply] using h
  · have h := congrArg g.equiv.symm hm
    simpa only [LinearEquiv.symm_apply_apply, map_sum, map_smul,
      CompactAutomorphism.symm_apply] using h

end

end ThirteenPlanes.AlbertGrading.CompletionO
