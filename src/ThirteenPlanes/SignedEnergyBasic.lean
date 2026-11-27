module

public import ThirteenPlanes.SignedSupport

@[expose] public section

set_option backward.privateInPublic true

/-! Single- and equal-share energies in the concrete signed carrier. -/

open scoped RealInnerProductSpace InnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

local notation "D" => signedDiagonalCubic
local notation "d" => signedEqualCubic


private theorem signedPlaneInclusion_inner_field (p : SignedPlaneIndex) (z : ℂ) (y : SignedField) :
    ⟪signedPlaneInclusion p z, y⟫_ℝ = 6 * (star z * signedPlaneCoordinates y p).re := by
  have h := (signedPlane p).starProjection_inner_eq_zero y (signedPlaneInclusion p z) ⟨z, rfl⟩
  rw [inner_sub_left] at h
  calc
    _ = ⟪y, signedPlaneInclusion p z⟫_ℝ := real_inner_comm _ _
    _ = ⟪(signedPlane p).starProjection y, signedPlaneInclusion p z⟫_ℝ := sub_eq_zero.mp h
    _ = ⟪signedPlaneInclusion p z, (signedPlane p).starProjection y⟫_ℝ := real_inner_comm _ _
    _ = _ := by rw [signedPlane_starProjection_apply, signedPlaneInclusion_inner]

/-- The diagonal multiplication acts independently on the representative coordinates. -/
theorem signedDiagonalCubic_L_coords (x y : SignedField) :
    signedDiagonalCubic.L x y = ∑ p, signedPlaneInclusion p (star (signedPlaneCoordinates x p * signedPlaneCoordinates y p)) := by
  apply ext_inner_right ℝ
  intro z
  change signedDiagonalCubic.apply x y z = ⟪_, z⟫_ℝ
  rw [signedDiagonalCubic_rep_sum, Finset.mul_sum, sum_inner]
  simp only [signedPlaneInclusion_inner_field, star_star]

theorem signedDiagonalCubic_L_same_plane (p : SignedPlaneIndex) (z w : ℂ) :
    signedDiagonalCubic.L (signedPlaneInclusion p z) (signedPlaneInclusion p w) = signedPlaneInclusion p (star (z * w)) := by
  rw [signedDiagonalCubic_L_coords]
  simp only [signedPlaneCoordinates_inclusion]
  rw [Finset.sum_eq_single p]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem signedDiagonalCubic_L_distinct_planes {p q : SignedPlaneIndex} (hpq : p ≠ q)
    (z w : ℂ) : signedDiagonalCubic.L (signedPlaneInclusion p z) (signedPlaneInclusion q w) = 0 := by
  rw [signedDiagonalCubic_L_coords]
  simp only [signedPlaneCoordinates_inclusion]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : s = p
  · subst s
    simp [Pi.single_eq_of_ne hpq]
  · simp [Pi.single_eq_of_ne hs]

theorem signedDiagonalCubic_L_of_mem_distinct {p q : SignedPlaneIndex} (hpq : p ≠ q)
    {x y : SignedField} (hx : x ∈ signedPlane p) (hy : y ∈ signedPlane q) :
    signedDiagonalCubic.L x y = 0 := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  exact signedDiagonalCubic_L_distinct_planes hpq u v

private theorem samePlane_product_of_restriction (h : SymmetricCubic SignedField)
    (p : SignedPlaneIndex) (u v : ℂ)
    (hperp : ∀ (x y : signedPlane p) (z : (signedPlane p)ᗮ), h.apply x y z = 0)
    (hplane : ∀ w : ℂ, h.apply (signedPlaneInclusion p u) (signedPlaneInclusion p v)
      (signedPlaneInclusion p w) = 6 * (u * v * w).re) :
    h.L (signedPlaneInclusion p u) (signedPlaneInclusion p v) =
      signedPlaneInclusion p (star (u * v)) := by
  apply ext_inner_right ℝ
  intro w
  change h.apply (signedPlaneInclusion p u) (signedPlaneInclusion p v) w = _
  let P := (signedPlane p).starProjection w
  have hz : w - P ∈ (signedPlane p)ᗮ := (signedPlane p).sub_starProjection_mem_orthogonal w
  have hvan := hperp ⟨signedPlaneInclusion p u, ⟨u, rfl⟩⟩
    ⟨signedPlaneInclusion p v, ⟨v, rfl⟩⟩ ⟨w - P, hz⟩
  have hs := h.apply_add₃ (signedPlaneInclusion p u) (signedPlaneInclusion p v) P (w - P)
  rw [show P + (w - P) = w by abel] at hs
  change h.apply (signedPlaneInclusion p u) (signedPlaneInclusion p v) (w - P) = 0 at hvan
  rw [hs, hvan, add_zero]
  change h.apply (signedPlaneInclusion p u) (signedPlaneInclusion p v)
    ((signedPlane p).starProjection w) = _
  rw [signedPlane_starProjection_apply, hplane, signedPlaneInclusion_inner_field, star_star]

/-- The equal-strength product of two fields in one plane stays in that plane. -/
theorem signedEqualCubic_L_same_plane (p : SignedPlaneIndex) (u v : ℂ) :
    signedEqualCubic.L (signedPlaneInclusion p u) (signedPlaneInclusion p v) =
      signedPlaneInclusion p (star (u * v)) :=
  samePlane_product_of_restriction d p u v (signedEqualCubic_repeatedPlane p)
    (signedEqualCubic_on_same_plane p u v)

theorem signedDiagonalCubic_square_same_plane {p : SignedPlaneIndex} {x : SignedField}
    (hx : x ∈ signedPlane p) : signedDiagonalCubic.squareMap x ∈ signedPlane p ∧
      ‖signedDiagonalCubic.squareMap x‖ ^ 2 = ‖x‖ ^ 4 / 6 ∧ signedEqualCubic.squareMap x = signedDiagonalCubic.squareMap x := by
  rcases hx with ⟨z, rfl⟩
  rw [SymmetricCubic.squareMap, SymmetricCubic.squareMap, signedEqualCubic_L_same_plane,
    signedDiagonalCubic_L_same_plane]
  refine ⟨⟨_, rfl⟩, ?_, rfl⟩
  rw [signedPlaneInclusion_norm_sq, show ‖signedPlaneInclusion p z‖ ^ 4 =
    (‖signedPlaneInclusion p z‖ ^ 2) ^ 2 by ring, signedPlaneInclusion_norm_sq]
  simp only [Complex.star_def, Complex.norm_conj, norm_mul]
  ring

private theorem coupling_signedPair_D_d (a b : ℝ) :
    coupling signedPair (a, b) = (a - b) • D + b • d := by
  change a • D + b • (d - D) = (a - b) • D + b • d
  have hs₁ : b • (d - D) = b • d - b • D := smul_sub b d D
  have hs₂ : (a - b) • D = a • D - b • D := sub_smul a b D
  rw [hs₁, hs₂]
  abel

theorem signedEnergy_expand (a b : ℝ) (x : SignedField) :
    unitEnergy (coupling signedPair (a, b)) x =
      6 * ((a - b)^2 * ‖signedDiagonalCubic.squareMap x‖ ^ 2 +
        2 * (a - b) * b * ⟪signedDiagonalCubic.squareMap x, signedEqualCubic.squareMap x⟫_ℝ + b^2 * ‖signedEqualCubic.squareMap x‖ ^ 2) := by
  rw [unitEnergy, coupling_signedPair_D_d, SymmetricCubic.squareMap_add,
    SymmetricCubic.squareMap_smul, SymmetricCubic.squareMap_smul, norm_add_sq_real,
    norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Every unit field in any signed plane has energy `a²` at coupling `(a,b)`. -/
theorem signed_singleEnergy {p : SignedPlaneIndex} {x : SignedField}
    (hx : x ∈ signedPlane p) (nx : ‖x‖ = 1) (a b : ℝ) :
    unitEnergy (coupling signedPair (a, b)) x = a ^ 2 := by
  obtain ⟨_, hn, he⟩ := signedDiagonalCubic_square_same_plane hx
  rw [signedEnergy_expand, he, real_inner_self_eq_norm_sq, hn, nx]
  ring

/-- The unit equal share of two orthogonal unit directions. -/
def signedTwoShare (x y : SignedField) : SignedField := (Real.sqrt 2)⁻¹ • (x + y)

theorem signed_norm_rescaled_by_sqrt (x : SignedField) (N : ℝ) (hN : 0 < N)
    (hx : ‖x‖ ^ 2 = N) : ‖(Real.sqrt N)⁻¹ • x‖ = 1 := by
  have h : ‖x‖ = Real.sqrt N := by rw [← hx, Real.sqrt_sq (norm_nonneg _)]
  rw [norm_smul, h, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hN)),
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hN)]

theorem signedTwoShare_unit {p q : SignedPlaneIndex} (hpq : p ≠ q) {x y : SignedField}
    (hx : x ∈ signedPlane p) (hy : y ∈ signedPlane q) (nx : ‖x‖ = 1) (ny : ‖y‖ = 1) :
    ‖signedTwoShare x y‖ = 1 := by
  apply signed_norm_rescaled_by_sqrt _ 2 (by norm_num)
  rw [norm_add_sq_real, (signedPlane_pairwise_orthogonal hpq).inner_eq hx hy, nx, ny]
  norm_num

theorem signed_squareMap_field_smul (h : SymmetricCubic SignedField) (c : ℝ) (x : SignedField) :
    h.squareMap (c • x) = c ^ 2 • h.squareMap x := by
  simp [SymmetricCubic.squareMap, smul_smul, pow_two]

theorem signed_squareMap_field_add (h : SymmetricCubic SignedField) (x y : SignedField) :
    h.squareMap (x + y) = h.squareMap x + h.squareMap y + (2 : ℝ) • h.L x y := by
  simp only [SymmetricCubic.squareMap, map_add, LinearMap.add_apply, h.L_comm y x, two_smul]
  abel

private theorem signedEqualCubic_mixed_inner_zero {p q : SignedPlaneIndex} (hpq : p ≠ q)
    {x y z : SignedField} (hx : x ∈ signedPlane p) (hy : y ∈ signedPlane q)
    (hz : z ∈ signedPlane p) : ⟪signedEqualCubic.L x y, z⟫_ℝ = 0 := by
  change signedEqualCubic.apply x y z = 0
  rw [signedEqualCubic.apply_swap₂₃]
  exact signedEqualCubic_repeatedPlane p ⟨x, hx⟩ ⟨z, hz⟩
    ⟨y, (signedPlane_pairwise_orthogonal hpq.symm) hy⟩

/-- The equal two-plane share at all homogeneous couplings and all unit angles. -/
theorem signed_twoEnergy (law : HasSquareLaw d) {p q : SignedPlaneIndex} (hpq : p ≠ q)
    {x y : SignedField} (hx : x ∈ signedPlane p) (hy : y ∈ signedPlane q)
    (nx : ‖x‖ = 1) (ny : ‖y‖ = 1) (a b : ℝ) :
    unitEnergy (coupling signedPair (a, b)) (signedTwoShare x y) = (a ^ 2 + b ^ 2) / 2 := by
  let n := signedTwoShare x y
  let A := signedDiagonalCubic.squareMap x + signedDiagonalCubic.squareMap y
  have hs : ((Real.sqrt 2)⁻¹)^2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num), one_div]
  have hn : ‖n‖ = 1 := signedTwoShare_unit hpq hx hy nx ny
  obtain ⟨hxD, hxnorm, hxd⟩ := signedDiagonalCubic_square_same_plane hx
  obtain ⟨hyD, hynorm, hyd⟩ := signedDiagonalCubic_square_same_plane hy
  have hA : ‖A‖ ^ 2 = 1 / 3 := by
    change ‖signedDiagonalCubic.squareMap x + signedDiagonalCubic.squareMap y‖ ^ 2 = _
    rw [norm_add_sq_real, (signedPlane_pairwise_orthogonal hpq).inner_eq hxD hyD,
      hxnorm, hynorm, nx, ny]
    norm_num
  have hDxy := signedDiagonalCubic_L_of_mem_distinct hpq hx hy
  have hdiag : signedDiagonalCubic.squareMap n = (1 / 2 : ℝ) • A := by
    unfold n signedTwoShare A
    rw [signed_squareMap_field_smul, hs, signed_squareMap_field_add, hDxy, smul_zero, add_zero]
  have hd : signedEqualCubic.squareMap n = (1 / 2 : ℝ) • (A + (2 : ℝ) • signedEqualCubic.L x y) := by
    unfold n signedTwoShare A
    rw [signed_squareMap_field_smul, hs, signed_squareMap_field_add, hxd, hyd]
  have hcross : ⟪A, signedEqualCubic.L x y⟫_ℝ = 0 := by
    rw [real_inner_comm]
    change ⟪signedEqualCubic.L x y, signedDiagonalCubic.squareMap x + signedDiagonalCubic.squareMap y⟫_ℝ = 0
    rw [inner_add_right, signedEqualCubic_mixed_inner_zero hpq hx hy hxD, signedEqualCubic.L_comm x y,
      signedEqualCubic_mixed_inner_zero hpq.symm hy hx hyD, add_zero]
  have hdiagNorm : ‖signedDiagonalCubic.squareMap n‖ ^ 2 = 1 / 12 := by
    rw [hdiag, norm_smul, mul_pow, hA]
    norm_num
  have hdNorm : ‖signedEqualCubic.squareMap n‖ ^ 2 = 1 / 6 := by rw [law n, hn]; norm_num
  have hinner : ⟪signedDiagonalCubic.squareMap n, signedEqualCubic.squareMap n⟫_ℝ = 1 / 12 := by
    rw [hdiag, hd, real_inner_smul_left, real_inner_smul_right, inner_add_right,
      real_inner_smul_right, hcross, real_inner_self_eq_norm_sq, hA]
    norm_num
  change unitEnergy (coupling signedPair (a, b)) n = _
  rw [signedEnergy_expand, hdiagNorm, hdNorm, hinner]
  ring

end

end ThirteenPlanes
