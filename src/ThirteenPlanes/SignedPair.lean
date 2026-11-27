module

public import ThirteenPlanes.Cubic
public import ThirteenPlanes.SignedCoefficients
public import ThirteenPlanes.SignedPlanes

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

private def signedCoordinate (i : NonzeroCharge) : SignedField →ₗ[ℝ] ℂ :=
  (LinearMap.proj i).comp signedCoordinates

private def coefficientTerm (a : ℂ) (i j k : NonzeroCharge) :
    SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => Complex.reCLM.toLinearMap.comp
      ((LinearMap.mulLeft ℝ (a * signedCoordinate i x * signedCoordinate j y)).comp
        (signedCoordinate k)))
    (by intros; ext z; simp [mul_add, add_mul, mul_assoc])
    (by
      intros
      ext z
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, map_smul, LinearMap.smul_apply,
        mul_smul_comm, smul_mul_assoc])
    (by intros; ext z; simp [mul_add, add_mul, mul_assoc])
    (by
      intros
      ext z
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, map_smul, LinearMap.smul_apply,
        mul_smul_comm, smul_mul_assoc])

private theorem coefficientTerm_apply (a : ℂ) (i j k : NonzeroCharge) (x y z : SignedField) :
    coefficientTerm a i j k x y z =
      (a * signedCoordinates x i * signedCoordinates y j * signedCoordinates z k).re :=
  rfl

private def signedTrilinear (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ) :
    SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ :=
  ∑ i, ∑ j, ∑ k, coefficientTerm (c i j k) i j k

private theorem signedTrilinear_apply (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (x y z : SignedField) :
    signedTrilinear c x y z =
      ∑ i, ∑ j, ∑ k, (c i j k * signedCoordinates x i * signedCoordinates y j *
        signedCoordinates z k).re := by
  simp only [signedTrilinear, LinearMap.sum_apply, coefficientTerm_apply]

private theorem signedTrilinear_swap_first
    (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (hs : ∀ i j k, c i j k = c j i k) (x y z : SignedField) :
    signedTrilinear c x y z = signedTrilinear c y x z := by
  simp only [signedTrilinear_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [hs j i k]
  congr 1
  ring

private theorem signedTrilinear_swap_last
    (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (hs : ∀ i j k, c i j k = c i k j) (x y z : SignedField) :
    signedTrilinear c x y z = signedTrilinear c x z y := by
  simp only [signedTrilinear_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hs i k j]
  congr 1
  ring

/-- A symmetric signed coefficient table induces a real tensor by polarization. -/
def cubicFromTable (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (h₁ : ∀ i j k, c i j k = c j i k) (h₂ : ∀ i j k, c i j k = c i k j) :
    SymmetricCubic SignedField :=
  SymmetricCubic.ofPolarization (signedTrilinear c)
    (signedTrilinear_swap_first c h₁) (signedTrilinear_swap_last c h₂)

theorem cubicFromTable_apply (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (h₁ : ∀ i j k, c i j k = c j i k) (h₂ : ∀ i j k, c i j k = c i k j) (x y z : SignedField) :
    (cubicFromTable c h₁ h₂).apply x y z =
      ∑ i, ∑ j, ∑ k, (c i j k * signedCoordinates x i * signedCoordinates y j *
        signedCoordinates z k).re := by
  simp only [cubicFromTable, SymmetricCubic.apply_ofPolarization, signedTrilinear_apply]

theorem signedCoefficient_swap_last (i j k : NonzeroCharge) :
    signedCoefficient i j k = signedCoefficient i k j :=
  (signedCoefficient_cycle i j k).trans
    ((signedCoefficient_swap_first j k i).trans (signedCoefficient_cycle i k j).symm)

/-- The real equal-strength tensor of the signed model. -/
def signedEqualCubic : SymmetricCubic SignedField :=
  cubicFromTable signedCoefficient signedCoefficient_swap_first signedCoefficient_swap_last

theorem signedEqualCubic_apply (x y z : SignedField) :
    signedEqualCubic.apply x y z =
      ∑ i, ∑ j, ∑ k, (signedCoefficient i j k * signedCoordinates x i * signedCoordinates y j *
        signedCoordinates z k).re :=
  cubicFromTable_apply _ _ _ _ _ _

/-- Evaluate the real tensor by taking the real part after summing the complex table. -/
theorem signedEqualCubic_re_sum (x y z : SignedField) :
    signedEqualCubic.apply x y z =
      (∑ i, ∑ j, ∑ k, signedCoefficient i j k * signedCoordinates x i *
        signedCoordinates y j * signedCoordinates z k).re := by
  simp only [signedEqualCubic_apply, Complex.re_sum]

/-- The diagonal tensor keeps the repeated nonzero charge triples. -/
def signedDiagonalCoefficient (i j k : NonzeroCharge) : ℂ :=
  if i = j ∧ j = k then 3 else 0

private theorem diagonalSwapFirst (i j k : NonzeroCharge) :
    signedDiagonalCoefficient i j k = signedDiagonalCoefficient j i k := by
  have h : (i = j ∧ j = k) ↔ (j = i ∧ i = k) := by
    constructor <;> rintro ⟨rfl, rfl⟩ <;> simp
  simp only [signedDiagonalCoefficient, h]

private theorem diagonalSwapLast (i j k : NonzeroCharge) :
    signedDiagonalCoefficient i j k = signedDiagonalCoefficient i k j := by
  have h : (i = j ∧ j = k) ↔ (i = k ∧ k = j) := by
    constructor <;> rintro ⟨rfl, rfl⟩ <;> simp
  simp only [signedDiagonalCoefficient, h]

/-- The sum of the single-plane cubics in the signed model. -/
def signedDiagonalCubic : SymmetricCubic SignedField :=
  cubicFromTable signedDiagonalCoefficient diagonalSwapFirst diagonalSwapLast

theorem signedDiagonalCubic_apply (x y z : SignedField) :
    signedDiagonalCubic.apply x y z =
      ∑ i, ∑ j, ∑ k, (signedDiagonalCoefficient i j k *
        signedCoordinates x i * signedCoordinates y j * signedCoordinates z k).re :=
  cubicFromTable_apply _ _ _ _ _ _

private theorem charge_triple (x : Charge) : x + x + x = 0 := by
  funext i
  change x i + x i + x i = 0
  linear_combination x i * (by decide : (3 : ZMod 3) = 0)

theorem signedCoefficient_zero_of_grade_sum_ne_zero (i j k : NonzeroCharge)
    (h : i.val + j.val + k.val ≠ 0) : signedCoefficient i j k = 0 := by
  simp [signedCoefficient, gradeMetric, h]

@[simp] theorem signedCoefficient_diagonal (i : NonzeroCharge) :
    signedCoefficient i i i = 3 := by
  simp [signedCoefficient, gradeMetric, charge_triple, gradedProductCoefficient, dependentGrades]

theorem signedCoefficient_repeated_first (i k : NonzeroCharge) :
    signedCoefficient i i k = signedDiagonalCoefficient i i k := by
  by_cases h : i = k
  · subst k
    simp [signedDiagonalCoefficient]
  · have hn : i.val + i.val + k.val ≠ 0 := by
      intro hz
      apply h
      apply Subtype.ext
      linear_combination charge_triple i.val - hz
    simp [signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ hn, signedDiagonalCoefficient, h]

/-- The literal off-line phases use the manuscript's root with positive imaginary part. -/
theorem signedCoefficient_offLine :
    signedCoefficient ⟨![1,0,0], by decide⟩ ⟨![2,2,1], by decide⟩ ⟨![0,1,2], by decide⟩ =
      3 * (1 + Complex.I * (Real.sqrt 3 : ℝ)) / 4 := by
  change gradedProductCoefficient ![1,0,0] ![2,2,1] * gradeMetric (![1,0,0] + ![2,2,1]) ![0,1,2] = _
  have h : (![1,0,0] : Charge) + ![2,2,1] + ![0,1,2] = 0 := by decide
  rw [gradedProductCoefficient_offLine, gradeMetric, ite_eq_left h]
  ring

theorem signedDiagonalCubic_sum (x y z : SignedField) :
    signedDiagonalCubic.apply x y z =
      3 * ∑ i, (signedCoordinates x i * signedCoordinates y i * signedCoordinates z i).re := by
  rw [signedDiagonalCubic_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp only [signedDiagonalCoefficient, and_self, ↓reduceIte]
      rw [show (3 : ℂ) * signedCoordinates x i * signedCoordinates y i * signedCoordinates z i =
        3 * (signedCoordinates x i * signedCoordinates y i * signedCoordinates z i) by ring, Complex.mul_re]
      norm_num
    · intro k _ hki
      simp [signedDiagonalCoefficient, Ne.symm hki]
    · simp
  · intro j _ hji
    simp [signedDiagonalCoefficient, Ne.symm hji]
  · simp

/-- The diagonal polynomial has coefficient six in each representative complex coordinate. -/
theorem signedDiagonalCubic_normalization (x : SignedField) :
    signedDiagonalCubic.apply x x x =
      6 * ∑ p, ((signedPlaneCoordinates x p) ^ 3).re := by
  rw [signedDiagonalCubic_sum]
  simp only [← pow_three']
  rw [← signedPlaneGradeEquiv.sum_comp (fun i => (signedCoordinates x i ^ 3).re),
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, signedPlaneGradeEquiv_true, signedPlaneGradeEquiv_false,
    signedCoordinates_opposite, Complex.star_def, ← map_pow, Complex.conj_re,
    ← signedPlaneCoordinates_apply, ← two_mul, ← Finset.mul_sum]
  ring

/-- The signed model's homogeneous pair of diagonal and mixing couplings. -/
def signedPair : CubicPair SignedField where
  diagonalCubic := signedDiagonalCubic
  mixingCubic := signedEqualCubic - signedDiagonalCubic

@[simp] theorem signedPair_at_one : interactionCubic signedPair 1 = signedEqualCubic := by
  simp only [interactionCubic_one, signedPair]
  abel

end

end ThirteenPlanes
