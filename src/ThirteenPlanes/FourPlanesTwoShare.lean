/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FourPlanesEnergy

@[expose] public section

/-! The equal-share energy for arbitrary unit directions in two distinct matrix planes. -/

noncomputable section

namespace ThirteenPlanes

open TracelessHermitian3

theorem matrixSquare_fixed (k : Fin 4) (x : TracelessHermitian3)
    (hx : matrixFrameProjection k x = x) : matrixFrameProjection k (square x) = square x := by
  rw [← jordan_self, project_jordan_of_fixed _ _ _ hx hx]

theorem matrixDiagonalSquare_add_distinct (k l : Fin 4) (hkl : k ≠ l) (x y : TracelessHermitian3)
    (hx : matrixFrameProjection k x = x) (hy : matrixFrameProjection l y = y) :
    matrixDiagonalCubic.squareMap (x + y) = square x + square y := by
  rw [matrixDiagonalCubic_squareMap]
  simp_rw [map_add, matrixFrameProjection_fixed _ k _ hx, matrixFrameProjection_fixed _ l _ hy]
  have hterm (i : Fin 4) :
      square ((if i = k then x else 0) + (if i = l then y else 0)) =
        (if i = k then square x else 0) + (if i = l then square y else 0) := by
    by_cases hik : i = k
    · subst i
      simp [hkl]
    · by_cases hil : i = l <;> simp [hik, hil, hkl.symm]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib]

theorem inner_jordan_zero_of_planes (k l : Fin 4) (hkl : k ≠ l)
    (x y z : TracelessHermitian3) (hx : matrixFrameProjection k x = x)
    (hy : matrixFrameProjection l y = y) (hz : matrixFrameProjection k z = z) :
    inner ℝ (jordan x y) z = 0 := by
  rw [inner_jordan_swap]
  exact matrixFrameOrthogonality k l hkl _ _ (project_jordan_of_fixed k x z hx hz) hy

/-- The normalized equal share of the unit fields in two different matrix planes. -/
def matrixTwoShare (x y : TracelessHermitian3) : TracelessHermitian3 :=
  (Real.sqrt 2)⁻¹ • (x + y)

theorem matrixTwoShare_unit (k l : Fin 4) (hkl : k ≠ l) (x y : TracelessHermitian3)
    (hx : matrixFrameProjection k x = x) (hy : matrixFrameProjection l y = y)
    (nx : ‖x‖ = 1) (ny : ‖y‖ = 1) : ‖matrixTwoShare x y‖ = 1 := by
  apply norm_rescaled_by_sqrt _ 2 (by norm_num)
  rw [norm_add_sq_real, matrixFrameOrthogonality k l hkl x y hx hy, nx, ny]
  norm_num

theorem fourPlane_twoEnergy (k l : Fin 4) (hkl : k ≠ l) (x y : TracelessHermitian3)
    (hx : matrixFrameProjection k x = x) (hy : matrixFrameProjection l y = y)
    (nx : ‖x‖ = 1) (ny : ‖y‖ = 1) (a b : ℝ) :
    unitEnergy (coupling fourPlanePair (a, b)) (matrixTwoShare x y) =
      (a ^ 2 + b ^ 2) / 2 := by
  let n := matrixTwoShare x y
  let A := square x + square y
  have hs : ((Real.sqrt 2)⁻¹)^2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num), one_div]
  have hna : ‖n‖ = 1 := matrixTwoShare_unit k l hkl x y hx hy nx ny
  have hA : ‖A‖^2 = 1 / 3 := by
    change ‖square x + square y‖ ^ 2 = _
    rw [norm_add_sq_real,
      matrixFrameOrthogonality k l hkl _ _ (matrixSquare_fixed k x hx) (matrixSquare_fixed l y hy),
      square_norm_sq, square_norm_sq, nx, ny]
    norm_num
  have hdiag : matrixDiagonalCubic.squareMap n = (1 / 2 : ℝ) • A := by
    rw [matrixDiagonalCubic_squareMap]
    simp only [n, matrixTwoShare, map_smul, matrixSquare_smul, hs, ← Finset.smul_sum]
    rw [← matrixDiagonalCubic_squareMap, matrixDiagonalSquare_add_distinct k l hkl _ _ hx hy]
  have hcubic : square n = (1 / 2 : ℝ) • (A + 2 • jordan x y) := by
    change square ((Real.sqrt 2)⁻¹ • (x + y)) = _
    rw [matrixSquare_smul, hs]
    congr 1
    simp only [← jordan_self, A, map_add, LinearMap.add_apply, two_nsmul, jordan_comm y x]
    abel
  have hcross : inner ℝ A (jordan x y) = 0 := by
    rw [real_inner_comm (jordan x y) A]
    change inner ℝ (jordan x y) (square x + square y) = 0
    rw [inner_add_right, inner_jordan_zero_of_planes k l hkl x y (square x) hx hy
      (matrixSquare_fixed k x hx), jordan_comm x y,
      inner_jordan_zero_of_planes l k hkl.symm y x (square y) hy hx
      (matrixSquare_fixed l y hy), add_zero]
  have hnormQ₀ : ‖matrixDiagonalCubic.squareMap n‖^2 = 1/12 := by
    rw [hdiag, norm_smul, mul_pow, hA]
    norm_num
  have hnormQ₁ : ‖square n‖^2 = 1/6 := by rw [square_norm_sq, hna]; norm_num
  have hcrossQ : inner ℝ (matrixDiagonalCubic.squareMap n) (square n) = 1/12 := by
    have htwo : inner ℝ A (2 • jordan x y) = 0 := by
      rw [two_nsmul, inner_add_right A (jordan x y) (jordan x y), hcross, add_zero]
    rw [hdiag, hcubic, real_inner_smul_left A, real_inner_smul_right A, inner_add_right A A,
      htwo, real_inner_self_eq_norm_sq A, hA]
    ring
  change unitEnergy (coupling fourPlanePair (a, b)) n = _
  rw [unitEnergy, coupling_fourPlanePair, SymmetricCubic.squareMap_add, SymmetricCubic.squareMap_smul,
    SymmetricCubic.squareMap_smul, matrixEqualCubic_squareMap, norm_add_sq_real, norm_smul, norm_smul,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hnormQ₀, hnormQ₁,
    real_inner_smul_left (matrixDiagonalCubic.squareMap n),
    real_inner_smul_right (matrixDiagonalCubic.squareMap n), hcrossQ]
  ring

def fourPlaneMarkedOne : TracelessHermitian3 := (Real.sqrt 6)⁻¹ • matrixCorner 0 0

def fourPlaneMarkedTwo : TracelessHermitian3 :=
  matrixTwoShare fourPlaneMarkedOne ((Real.sqrt 6)⁻¹ • matrixCorner 1 0)

theorem fourPlaneEnergyTests :
    EnergyTests fourPlanePair fourPlaneMarkedOne fourPlaneMarkedTwo fourPlaneMarkedThree := by
  have hunit (k : Fin 4) (j : Fin 3) : ‖(Real.sqrt 6)⁻¹ • matrixCorner k j‖ = 1 :=
    norm_rescaled_by_sqrt _ _ (by norm_num) (matrixCorner_norm_sq k j)
  have hfixed (k : Fin 4) (j : Fin 3) : matrixFrameProjection k
      ((Real.sqrt 6)⁻¹ • matrixCorner k j) = (Real.sqrt 6)⁻¹ • matrixCorner k j := by
    rw [map_smul, matrixCorner_fixed]
  refine ⟨hunit _ _, matrixTwoShare_unit 0 1 (by decide) _ _ (hfixed _ _) (hfixed _ _)
    (hunit _ _) (hunit _ _), fourPlaneMarkedThree_unit, ?_, ?_, ?_, fourPlane_squareLaw⟩
  · rintro ⟨a, b⟩
    exact fourPlane_singleEnergy 0 _ (hfixed _ _) (hunit _ _) a b
  · rintro ⟨a, b⟩
    exact fourPlane_twoEnergy 0 1 (by decide) _ _ (hfixed _ _) (hfixed _ _)
      (hunit _ _) (hunit _ _) a b
  · rintro ⟨a, b⟩
    exact fourPlaneMarkedThree_energy a b

end ThirteenPlanes
