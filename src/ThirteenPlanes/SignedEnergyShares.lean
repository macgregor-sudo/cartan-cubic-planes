module

public import ThirteenPlanes.SignedEnergyBasic
public import ThirteenPlanes.Weyl

@[expose] public section

set_option backward.privateInPublic true

/-! The marked signed three-plane share and the concrete energy test fields. -/

open scoped RealInnerProductSpace InnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

local notation "d" => signedEqualCubic

/-- The standard-basis corner has grade `(0,1,0)` and representative coordinate `1`. -/
def signedMarkedPlaneOne : SignedPlaneIndex := ⟨⟨![0, 1, 0], by decide⟩, by decide⟩

/-- The flat corner has grade `(1,0,0)` and representative coordinate `1`. -/
def signedMarkedPlaneTwo : SignedPlaneIndex := ⟨⟨![1, 0, 0], by decide⟩, by decide⟩

/-- The third corner has grade `(1,1,0)` and representative coordinate `chargeRoot`. -/
def signedMarkedPlaneThree : SignedPlaneIndex := ⟨⟨![1, 1, 0], by decide⟩, by decide⟩

def signedMarkedCornerOne : SignedField := signedPlaneInclusion signedMarkedPlaneOne 1

def signedMarkedCornerTwo : SignedField := signedPlaneInclusion signedMarkedPlaneTwo 1

def signedMarkedCornerThree : SignedField := signedPlaneInclusion signedMarkedPlaneThree chargeRoot

/-- The signed raw corners corresponding to `3qᵢ-I` under the marked Weyl-line identification. -/
def signedMarkedCornerTriple : SignedField :=
  signedMarkedCornerOne + signedMarkedCornerTwo + signedMarkedCornerThree

def signedMarkedOne : SignedField := (Real.sqrt 6)⁻¹ • signedMarkedCornerOne

def signedMarkedTwo : SignedField := signedTwoShare signedMarkedOne
  ((Real.sqrt 6)⁻¹ • signedMarkedCornerTwo)

def signedMarkedThree : SignedField := (Real.sqrt 18)⁻¹ • signedMarkedCornerTriple

private theorem chargeRoot_norm_one : ‖chargeRoot‖ = 1 := by
  have hs : ‖chargeRoot‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, chargeRoot_re, chargeRoot_im]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h := Real.sqrt_sq (norm_nonneg chargeRoot)
  rw [hs, Real.sqrt_one] at h
  exact h.symm

private theorem marked_corners_norm_sq :
    ‖signedMarkedCornerOne‖ ^ 2 = 6 ∧ ‖signedMarkedCornerTwo‖ ^ 2 = 6 ∧
      ‖signedMarkedCornerThree‖ ^ 2 = 6 := by
  simp [signedMarkedCornerOne, signedMarkedCornerTwo, signedMarkedCornerThree,
    signedPlaneInclusion_norm_sq, chargeRoot_norm_one]

private theorem marked_corner₁_mem : signedMarkedCornerOne ∈ signedPlane signedMarkedPlaneOne :=
  ⟨1, rfl⟩

private theorem marked_corner₂_mem : signedMarkedCornerTwo ∈ signedPlane signedMarkedPlaneTwo :=
  ⟨1, rfl⟩

private theorem marked_corner₃_mem : signedMarkedCornerThree ∈ signedPlane signedMarkedPlaneThree :=
  ⟨chargeRoot, rfl⟩

private theorem marked_cornerTriple_norm_sq : ‖signedMarkedCornerTriple‖ ^ 2 = 18 := by
  obtain ⟨h₁, h₂, h₃⟩ := marked_corners_norm_sq
  unfold signedMarkedCornerTriple
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_left,
    (signedPlane_pairwise_orthogonal (by decide : signedMarkedPlaneOne ≠ signedMarkedPlaneTwo)).inner_eq
      marked_corner₁_mem marked_corner₂_mem,
    (signedPlane_pairwise_orthogonal (by decide : signedMarkedPlaneOne ≠ signedMarkedPlaneThree)).inner_eq
      marked_corner₁_mem marked_corner₃_mem,
    (signedPlane_pairwise_orthogonal (by decide : signedMarkedPlaneTwo ≠ signedMarkedPlaneThree)).inner_eq
      marked_corner₂_mem marked_corner₃_mem, h₁, h₂, h₃]
  norm_num

theorem signedMarkedThree_unit : ‖signedMarkedThree‖ = 1 :=
  signed_norm_rescaled_by_sqrt _ 18 (by norm_num) marked_cornerTriple_norm_sq

private theorem signedMarked_mixed_cubic :
    signedEqualCubic.apply signedMarkedCornerOne signedMarkedCornerTwo signedMarkedCornerThree = 3 / 2 := by
  unfold signedMarkedCornerOne signedMarkedCornerTwo signedMarkedCornerThree
  rw [signedEqualCubic_on_plane_inclusions, Fintype.sum_prod_type]
  let p := signedMarkedPlaneOne
  let q := signedMarkedPlaneTwo
  let r := signedMarkedPlaneThree
  have h₀₀ : signedCoefficient p.val (signedGrade q false) (signedGrade r false) = 0 :=
    signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ (by decide)
  have h₁₀ : signedCoefficient p.val (signedGrade q true) (signedGrade r false) = 0 :=
    signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ (by decide)
  have h₁₁ : signedCoefficient p.val (signedGrade q true) (signedGrade r true) = 0 :=
    signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ (by decide)
  have h₀₁ : signedCoefficient p.val (signedGrade q false) (signedGrade r true) = -3 / 2 := by
    have hgrade : p.val.val + (signedGrade q false).val + (signedGrade r true).val = 0 := by decide
    have hdep : ¬ dependentGrades p.val.val (signedGrade q false).val := by
      unfold dependentGrades
      decide
    have hexp : (gradeExponent p.val.val (signedGrade q false).val).val = 0 := by decide
    simp only [signedCoefficient, gradeMetric, hgrade, ↓reduceIte, gradedProductCoefficient,
      hdep, hexp, pow_zero]
    ring
  change 2 * ∑ i : Bool, ∑ j : Bool,
    (signedCoefficient p.val (signedGrade q i) (signedGrade r j) * 1 *
      signedGradeCoordinate i 1 * signedGradeCoordinate j chargeRoot).re = _
  simp only [Fintype.sum_bool, h₀₀, h₁₀, h₁₁, h₀₁, signedGradeCoordinate, ↓reduceIte,
    Bool.false_eq_true, zero_mul, Complex.zero_re, mul_one,
    Complex.star_def, Complex.mul_re, Complex.conj_re, chargeRoot_re]
  norm_num

private theorem signedCubic_apply_triple_sum (h : SymmetricCubic SignedField) (x y z : SignedField) :
    h.apply (x + y + z) (x + y + z) (x + y + z) =
      h.apply x x x + h.apply y y y + h.apply z z z +
      3 * (h.apply x x y + h.apply x x z + h.apply x y y + h.apply x z z +
        h.apply y y z + h.apply y z z) + 6 * h.apply x y z := by
  simp only [h.apply_add₁, h.apply_add₂, h.apply_add₃]
  simp only [h.apply_swap₁₂ y x, h.apply_swap₁₂ z x, h.apply_swap₁₂ z y,
    h.apply_swap₂₃ _ y x, h.apply_swap₂₃ _ z x, h.apply_swap₂₃ _ z y]
  ring

/-- The signed raw three-corner sum has cubic value 27. -/
theorem signedMarkedCornerTriple_cubic :
    signedEqualCubic.apply signedMarkedCornerTriple signedMarkedCornerTriple signedMarkedCornerTriple = 27 := by
  have hmixed := signedMarked_mixed_cubic
  unfold signedMarkedCornerTriple
  rw [signedCubic_apply_triple_sum, hmixed]
  rw [signedEqualCubic.apply_swap₁₂ signedMarkedCornerOne signedMarkedCornerTwo signedMarkedCornerTwo,
    signedEqualCubic.apply_swap₂₃ signedMarkedCornerTwo signedMarkedCornerOne signedMarkedCornerTwo,
    signedEqualCubic.apply_swap₁₂ signedMarkedCornerOne signedMarkedCornerThree signedMarkedCornerThree,
    signedEqualCubic.apply_swap₂₃ signedMarkedCornerThree signedMarkedCornerOne signedMarkedCornerThree,
    signedEqualCubic.apply_swap₁₂ signedMarkedCornerTwo signedMarkedCornerThree signedMarkedCornerThree,
    signedEqualCubic.apply_swap₂₃ signedMarkedCornerThree signedMarkedCornerTwo signedMarkedCornerThree]
  unfold signedMarkedCornerOne signedMarkedCornerTwo signedMarkedCornerThree
  rw [signedEqualCubic_on_exactly_two_planes (by decide : signedMarkedPlaneOne ≠ signedMarkedPlaneTwo),
    signedEqualCubic_on_exactly_two_planes (by decide : signedMarkedPlaneOne ≠ signedMarkedPlaneThree),
    signedEqualCubic_on_exactly_two_planes (by decide : signedMarkedPlaneTwo ≠ signedMarkedPlaneOne),
    signedEqualCubic_on_exactly_two_planes (by decide : signedMarkedPlaneThree ≠ signedMarkedPlaneOne),
    signedEqualCubic_on_exactly_two_planes (by decide : signedMarkedPlaneTwo ≠ signedMarkedPlaneThree),
    signedEqualCubic_on_exactly_two_planes (by decide : signedMarkedPlaneThree ≠ signedMarkedPlaneTwo)]
  simp only [signedEqualCubic_on_same_plane, ← pow_three', chargeRoot_cube]
  norm_num

private theorem squareMap_sum_three_fixed (h : SymmetricCubic SignedField) (x y z : SignedField)
    (hx : h.squareMap x = x) (hy : h.squareMap y = y) (hz : h.squareMap z = z)
    (hxy : h.L x y = 0) (hxz : h.L x z = 0) (hyz : h.L y z = 0) :
    h.squareMap (x + y + z) = x + y + z := by
  simp only [signed_squareMap_field_add, hx, hy, hz, map_add, LinearMap.add_apply,
    hxy, hxz, hyz, add_zero, smul_zero]

private theorem squareMap_corner_fixed (p : SignedPlaneIndex) (z : ℂ) (hz : star (z * z) = z) :
    signedDiagonalCubic.squareMap (signedPlaneInclusion p z) = signedPlaneInclusion p z := by
  rw [SymmetricCubic.squareMap, signedDiagonalCubic_L_same_plane, hz]

private theorem signedMarkedCornerTriple_diagonalSquare :
    signedDiagonalCubic.squareMap signedMarkedCornerTriple = signedMarkedCornerTriple := by
  have h₁ : signedDiagonalCubic.squareMap signedMarkedCornerOne = signedMarkedCornerOne :=
    squareMap_corner_fixed signedMarkedPlaneOne 1 (by simp)
  have h₂ : signedDiagonalCubic.squareMap signedMarkedCornerTwo = signedMarkedCornerTwo :=
    squareMap_corner_fixed signedMarkedPlaneTwo 1 (by simp)
  have h₃ : signedDiagonalCubic.squareMap signedMarkedCornerThree = signedMarkedCornerThree :=
    squareMap_corner_fixed signedMarkedPlaneThree chargeRoot (by
      rw [← pow_two chargeRoot, chargeRoot_sq_eq_star, star_star])
  have h₁₂ := signedDiagonalCubic_L_of_mem_distinct
    (by decide : signedMarkedPlaneOne ≠ signedMarkedPlaneTwo) marked_corner₁_mem marked_corner₂_mem
  have h₁₃ := signedDiagonalCubic_L_of_mem_distinct
    (by decide : signedMarkedPlaneOne ≠ signedMarkedPlaneThree) marked_corner₁_mem marked_corner₃_mem
  have h₂₃ := signedDiagonalCubic_L_of_mem_distinct
    (by decide : signedMarkedPlaneTwo ≠ signedMarkedPlaneThree) marked_corner₂_mem marked_corner₃_mem
  exact squareMap_sum_three_fixed signedDiagonalCubic signedMarkedCornerOne signedMarkedCornerTwo
    signedMarkedCornerThree h₁ h₂ h₃ h₁₂ h₁₃ h₂₃

/-- The signed marked three-plane share has the normalized homogeneous energy from Proposition 3.1. -/
theorem signedMarkedThree_energy (law : HasSquareLaw d) (a b : ℝ) :
    unitEnergy (coupling signedPair (a, b)) signedMarkedThree = (a^2 + a*b + b^2) / 3 := by
  have hs : ((Real.sqrt 18)⁻¹)^2 = (1 / 18 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num), one_div]
  have hD : signedDiagonalCubic.squareMap signedMarkedThree = (1/18 : ℝ) • signedMarkedCornerTriple := by
    rw [signedMarkedThree, signed_squareMap_field_smul, hs, signedMarkedCornerTriple_diagonalSquare]
  have hd : signedEqualCubic.squareMap signedMarkedThree = (1/18 : ℝ) • signedEqualCubic.squareMap signedMarkedCornerTriple := by
    rw [signedMarkedThree, signed_squareMap_field_smul, hs]
  have hDn : ‖signedDiagonalCubic.squareMap signedMarkedThree‖ ^ 2 = 1/18 := by
    rw [hD, norm_smul, mul_pow, marked_cornerTriple_norm_sq]
    norm_num
  have hdn : ‖signedEqualCubic.squareMap signedMarkedThree‖ ^ 2 = 1/6 := by
    rw [law, signedMarkedThree_unit]
    norm_num
  have hc : ⟪signedMarkedCornerTriple, signedEqualCubic.squareMap signedMarkedCornerTriple⟫_ℝ = 27 :=
    (real_inner_comm _ _).trans signedMarkedCornerTriple_cubic
  have hin : ⟪signedDiagonalCubic.squareMap signedMarkedThree,
      signedEqualCubic.squareMap signedMarkedThree⟫_ℝ = 1/12 := by
    rw [hD, hd, real_inner_smul_left, real_inner_smul_right, hc]
    norm_num
  rw [signedEnergy_expand, hDn, hdn, hin]
  ring

/-- The actual signed single-, two-, and marked three-plane fields supply the energy contract. -/
theorem signedEnergyTests (law : HasSquareLaw d) :
    EnergyTests signedPair signedMarkedOne signedMarkedTwo signedMarkedThree := by
  have hx : signedMarkedOne ∈ signedPlane signedMarkedPlaneOne :=
    (signedPlane _).smul_mem _ marked_corner₁_mem
  have hy : (Real.sqrt 6)⁻¹ • signedMarkedCornerTwo ∈ signedPlane signedMarkedPlaneTwo :=
    (signedPlane _).smul_mem _ marked_corner₂_mem
  have nx : ‖signedMarkedOne‖ = 1 :=
    signed_norm_rescaled_by_sqrt _ 6 (by norm_num) marked_corners_norm_sq.1
  have ny : ‖(Real.sqrt 6)⁻¹ • signedMarkedCornerTwo‖ = 1 :=
    signed_norm_rescaled_by_sqrt _ 6 (by norm_num) marked_corners_norm_sq.2.1
  have hne : signedMarkedPlaneOne ≠ signedMarkedPlaneTwo := by decide
  refine ⟨nx, signedTwoShare_unit hne hx hy nx ny, signedMarkedThree_unit, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a,b⟩
    exact signed_singleEnergy hx nx a b
  · rintro ⟨a,b⟩
    exact signed_twoEnergy law hne hx hy nx ny a b
  · rintro ⟨a,b⟩
    exact signedMarkedThree_energy law a b
  · rwa [signedPair_at_one]

end

end ThirteenPlanes
