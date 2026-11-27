module

public import ThirteenPlanes.PeirceDimensions
public import ThirteenPlanes.FourPlanesEnergy
public import ThirteenPlanes.FourPlanesPlaneData
public import ThirteenPlanes.PlaneContractions.Identities

@[expose] public section

/-! The unit-idempotent and trace-zero hypotheses hold in the four-plane matrix model. -/

namespace ThirteenPlanes.Peirce

open TracelessHermitian3

/-- A matrix corner yields Peirce spaces of dimensions three and four. -/
theorem fourPlane_unitIdempotent :
    ∃ (h : SymmetricCubic TracelessHermitian3) (a : TracelessHermitian3),
      IsRound h 1 ∧ IsUnitIdempotent h a ∧
        LinearMap.trace ℝ TracelessHermitian3 (h.L a) = 0 ∧
        Module.finrank ℝ (minusSpace h a) = 3 ∧ Module.finrank ℝ (halfSpace h a) = 4 := by
  let s : ℝ := Real.sqrt 6
  let x := matrixCorner 0 0
  let h := s • matrixEqualCubic
  let a := s⁻¹ • x
  have hs : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs₂ : s ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hx : ‖x‖ = s := by
    change ‖matrixCorner 0 0‖ = Real.sqrt 6
    calc
      _ = Real.sqrt (‖matrixCorner 0 0‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg (matrixCorner 0 0))).symm
      _ = _ := congrArg Real.sqrt (matrixCorner_norm_sq 0 0)
  have hround : IsRound h 1 := by
    refine ⟨by norm_num, fun y => ?_⟩
    rw [show h = s • matrixEqualCubic from rfl, SymmetricCubic.squareMap_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs, mul_pow, hs₂, matrixEqualCubic_squareMap, square_norm_sq]
    ring
  have ha : IsUnitIdempotent h a := by
    constructor
    · change ‖s⁻¹ • x‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), hx, inv_mul_cancel₀ hs.ne']
    · change (s • matrixEqualCubic).squareMap (s⁻¹ • x) = s⁻¹ • x
      have hscale : s * (s⁻¹) ^ 2 = s⁻¹ := by
        rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      rw [SymmetricCubic.squareMap_smul, matrixEqualCubic_squareMap, matrixSquare_smul,
        show square x = x from matrixCorner_square 0 0, smul_smul, hscale]
  have hcubic : matrixEqualCubic.TraceFree := by
    have ht := PlaneContractions.traceFree_interaction fourPlaneData
    rwa [interactionCubic_fourPlanePair_one] at ht
  have hzero : LinearMap.trace ℝ TracelessHermitian3 (h.L a) = 0 := by
    simp only [h, map_smul, LinearMap.smul_apply, smul_eq_mul, hcubic a, mul_zero]
  have hdim : Module.finrank ℝ TracelessHermitian3 = 8 := by
    simpa using finrank_eq_twice_card fourPlaneDecomposition
  obtain ⟨_, hm, hp⟩ := finrank_of_trace_zero hround ha hzero
  norm_num [hdim] at hm hp
  exact ⟨h, a, hround, ha, hzero, hm, hp⟩

end ThirteenPlanes.Peirce
