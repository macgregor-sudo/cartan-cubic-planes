module

public import ThirteenPlanes.SignedPair

@[expose] public section

set_option backward.privateInPublic true

/-! Complex matrices of real endomorphisms of the signed carrier, and the fact that the charge
coordinates of real fields span all complex coordinate vectors. -/

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

namespace SignedStabilizer

/-- Passing to the opposite grade, as a permutation of the nonzero grades. -/
def oppositeEquiv : NonzeroCharge ≃ NonzeroCharge where
  toFun := oppositeCharge
  invFun := oppositeCharge
  left_inv := oppositeCharge_opposite
  right_inv := oppositeCharge_opposite

@[simp] theorem oppositeEquiv_apply (x : NonzeroCharge) : oppositeEquiv x = oppositeCharge x := rfl

private theorem charge_neg_ne_self : ∀ x : Charge, x ≠ 0 → -x ≠ x := by decide

theorem oppositeCharge_ne (x : NonzeroCharge) : oppositeCharge x ≠ x := by
  intro h
  exact charge_neg_ne_self x.val x.property (congrArg Subtype.val h)

theorem oppositeCharge_injective : Function.Injective oppositeCharge :=
  oppositeEquiv.injective

theorem oppositeCharge_eq_iff {x y : NonzeroCharge} : oppositeCharge x = y ↔ x = oppositeCharge y := by
  constructor
  · rintro rfl; rw [oppositeCharge_opposite]
  · rintro rfl; rw [oppositeCharge_opposite]

/-- Sum over nonzero grades is unchanged by passing to opposite grades. -/
theorem sum_opposite {M : Type*} [AddCommMonoid M] (f : NonzeroCharge → M) :
    ∑ x, f (oppositeCharge x) = ∑ x, f x :=
  oppositeEquiv.sum_comp f

private def testCoord (x : NonzeroCharge) (θ : ℂ) (j : NonzeroCharge) : ℂ :=
  if j = x then θ else if j = oppositeCharge x then star θ else 0

private theorem testCoord_mem (x : NonzeroCharge) (θ : ℂ) : testCoord x θ ∈ signedFields := by
  intro j
  have hx := oppositeCharge_ne x
  by_cases h1 : j = x
  · subst j
    simp [testCoord, hx]
  · by_cases h2 : j = oppositeCharge x
    · subst j
      simp [testCoord, hx, oppositeCharge_opposite]
    · have h1' : oppositeCharge j ≠ x := fun h => h2 (oppositeCharge_eq_iff.mp h)
      have h2' : oppositeCharge j ≠ oppositeCharge x := fun h => h1 (oppositeCharge_injective h)
      simp [testCoord, h1, h2, h1', h2']

/-- The real field supported on the grades `x` and `-x`, with coordinate `θ` at `x`. -/
def testVec (x : NonzeroCharge) (θ : ℂ) : SignedField := ⟨testCoord x θ, testCoord_mem x θ⟩

theorem coord_testVec (x : NonzeroCharge) (θ : ℂ) (j : NonzeroCharge) :
    signedCoordinates (testVec x θ) j =
      if j = x then θ else if j = oppositeCharge x then star θ else 0 := rfl

theorem testVec_re_im (x : NonzeroCharge) (θ : ℂ) :
    testVec x θ = θ.re • testVec x 1 + θ.im • testVec x Complex.I := by
  apply Subtype.ext
  funext j
  change signedCoordinates (testVec x θ) j =
    θ.re • signedCoordinates (testVec x 1) j + θ.im • signedCoordinates (testVec x Complex.I) j
  simp only [coord_testVec]
  split_ifs <;> apply Complex.ext <;> simp

theorem testVec_opposite (x : NonzeroCharge) (θ : ℂ) :
    testVec (oppositeCharge x) θ = testVec x (star θ) := by
  apply Subtype.ext
  funext j
  change signedCoordinates (testVec (oppositeCharge x) θ) j = signedCoordinates (testVec x (star θ)) j
  have hx := oppositeCharge_ne x
  simp only [coord_testVec, oppositeCharge_opposite, star_star]
  by_cases h1 : j = x
  · subst j; simp [hx.symm]
  · by_cases h2 : j = oppositeCharge x <;> simp [h1, h2, hx]

theorem two_smul_eq_sum_testVec (u : SignedField) :
    (2 : ℝ) • u = ∑ x, testVec x (signedCoordinates u x) := by
  apply Subtype.ext
  funext j
  change signedCoordinates ((2 : ℝ) • u) j = signedCoordinates (∑ x, testVec x (signedCoordinates u x)) j
  rw [map_sum, Finset.sum_apply]
  simp only [coord_testVec]
  have hsplit : ∀ x : NonzeroCharge,
      (if j = x then signedCoordinates u x else
        if j = oppositeCharge x then star (signedCoordinates u x) else 0) =
      (if x = j then signedCoordinates u x else 0) +
        (if x = oppositeCharge j then star (signedCoordinates u x) else 0) := by
    intro x
    by_cases h1 : j = x
    · subst j
      simp only [↓reduceIte, (oppositeCharge_ne x).symm, add_zero]
    · have h1' : x ≠ j := fun h => h1 h.symm
      by_cases h2 : j = oppositeCharge x
      · have : x = oppositeCharge j := by rw [h2, oppositeCharge_opposite]
        have e1 : (j = oppositeCharge x) = True := eq_true h2
        have e2 : (x = oppositeCharge j) = True := eq_true this
        simp only [h1, h1', e1, e2, ↓reduceIte, zero_add]
      · have : x ≠ oppositeCharge j := fun h => h2 (by rw [h, oppositeCharge_opposite])
        simp only [h1, h2, h1', this, ↓reduceIte, add_zero]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    signedCoordinates_opposite, star_star, map_smul]
  change (2 : ℝ) • signedCoordinates u j = _
  rw [two_smul]

/-- The complex matrix of a real endomorphism in the charge coordinates. -/
def mat (A : SignedField →ₗ[ℝ] SignedField) : Matrix NonzeroCharge NonzeroCharge ℂ :=
  fun y x => (signedCoordinates (A (testVec x 1)) y -
    Complex.I * signedCoordinates (A (testVec x Complex.I)) y) / 2

private theorem coord_real_smul (r : ℝ) (v : SignedField) (j : NonzeroCharge) :
    signedCoordinates (r • v) j = (r : ℂ) * signedCoordinates v j := by
  rw [map_smul]; rfl

private theorem pair_alg (f1 fI ζ : ℂ) :
    (f1 - Complex.I * fI) / 2 * ζ + (f1 + Complex.I * fI) / 2 * star ζ =
      (ζ.re : ℂ) * f1 + (ζ.im : ℂ) * fI := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem coord_apply_eq_sum (A : SignedField →ₗ[ℝ] SignedField) (u : SignedField)
    (y : NonzeroCharge) :
    signedCoordinates (A u) y = ∑ x, mat A y x * signedCoordinates u x := by
  set f1 : NonzeroCharge → ℂ := fun x => signedCoordinates (A (testVec x 1)) y
  set fI : NonzeroCharge → ℂ := fun x => signedCoordinates (A (testVec x Complex.I)) y
  have hg : ∀ x, signedCoordinates (A (testVec x (signedCoordinates u x))) y =
      ((signedCoordinates u x).re : ℂ) * f1 x + ((signedCoordinates u x).im : ℂ) * fI x := by
    intro x
    rw [testVec_re_im, map_add, map_smul, map_smul, map_add, Pi.add_apply, coord_real_smul,
      coord_real_smul]
  have hlhs : (2 : ℂ) * signedCoordinates (A u) y =
      ∑ x, signedCoordinates (A (testVec x (signedCoordinates u x))) y := by
    have := congrArg (fun v => signedCoordinates (A v) y) (two_smul_eq_sum_testVec u)
    simp only [map_smul, map_sum, Finset.sum_apply] at this
    rw [← this]
    rfl
  have hf1 : ∀ x, f1 (oppositeCharge x) = f1 x := by
    intro x; simp only [f1, testVec_opposite, star_one]
  have hfI : ∀ x, fI (oppositeCharge x) = -fI x := by
    intro x
    simp only [fI, testVec_opposite, Complex.star_def, Complex.conj_I]
    rw [show testVec x (-Complex.I) = (-1 : ℝ) • testVec x Complex.I by
      rw [testVec_re_im x (-Complex.I)]; simp]
    rw [map_smul, coord_real_smul]; simp
  have hpair : ∀ x, mat A y x * signedCoordinates u x +
      mat A y (oppositeCharge x) * signedCoordinates u (oppositeCharge x) =
      signedCoordinates (A (testVec x (signedCoordinates u x))) y := by
    intro x
    rw [hg x, signedCoordinates_opposite]
    have hm1 : mat A y x = (f1 x - Complex.I * fI x) / 2 := rfl
    have hm2 : mat A y (oppositeCharge x) = (f1 x + Complex.I * fI x) / 2 := by
      change (f1 (oppositeCharge x) - Complex.I * fI (oppositeCharge x)) / 2 = _
      rw [hf1, hfI]; ring
    rw [hm1, hm2]
    exact pair_alg _ _ _
  have hsum : (2 : ℂ) * ∑ x, mat A y x * signedCoordinates u x =
      ∑ x, signedCoordinates (A (testVec x (signedCoordinates u x))) y := by
    rw [two_mul]
    conv_lhs => arg 2; rw [← sum_opposite]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hpair x
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact mul_left_cancel₀ h2 (hlhs.trans hsum.symm)

theorem coord_apply_eq_mulVec (A : SignedField →ₗ[ℝ] SignedField) (u : SignedField) :
    signedCoordinates (A u) = (mat A).mulVec (signedCoordinates u) := by
  funext y
  rw [coord_apply_eq_sum]
  rfl

/-- A real endomorphism with zero complex matrix is zero. -/
theorem eq_zero_of_mat_eq_zero (A : SignedField →ₗ[ℝ] SignedField) (h : mat A = 0) : A = 0 := by
  ext u
  apply Subtype.ext
  funext y
  change signedCoordinates (A u) y = signedCoordinates 0 y
  rw [coord_apply_eq_sum, h, map_zero]
  simp

theorem single_eq_testVec (x : NonzeroCharge) :
    (Pi.single x 1 : NonzeroCharge → ℂ) =
      (1 / 2 : ℂ) • (signedCoordinates (testVec x 1) -
        Complex.I • signedCoordinates (testVec x Complex.I)) := by
  funext j
  have hx := oppositeCharge_ne x
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, coord_testVec, Pi.single_apply]
  by_cases h1 : j = x
  · subst j; simp; ring
  · by_cases h2 : j = oppositeCharge x
    · simp [h2, hx, Complex.conj_I]
    · simp [h1, h2]

/-- A complex-linear map vanishing on the coordinates of all real fields is zero. -/
theorem linear_ext_of_real {N : Type*} [AddCommGroup N] [Module ℂ N]
    (φ : (NonzeroCharge → ℂ) →ₗ[ℂ] N) (h : ∀ a : SignedField, φ (signedCoordinates a) = 0) :
    φ = 0 := by
  apply (Pi.basisFun ℂ NonzeroCharge).ext
  intro x
  rw [Pi.basisFun_apply, single_eq_testVec, map_smul, map_sub, map_smul, h, h]
  simp

/-- A complex-trilinear form vanishing on real fields is zero. -/
theorem trilinear_ext_of_real
    (T : (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ a b c : SignedField,
      T (signedCoordinates a) (signedCoordinates b) (signedCoordinates c) = 0) : T = 0 := by
  have h1 : ∀ Z (b c : SignedField), T Z (signedCoordinates b) (signedCoordinates c) = 0 := by
    intro Z b c
    have := linear_ext_of_real ((T.flip (signedCoordinates b)).flip (signedCoordinates c))
      (fun a => h a b c)
    exact LinearMap.congr_fun this Z
  have h2 : ∀ Z W (c : SignedField), T Z W (signedCoordinates c) = 0 := by
    intro Z W c
    have := linear_ext_of_real ((T Z).flip (signedCoordinates c)) (fun b => h1 Z b c)
    exact LinearMap.congr_fun this W
  refine LinearMap.ext fun Z => LinearMap.ext fun W => LinearMap.ext fun U => ?_
  have := linear_ext_of_real (T Z W) (fun c => h2 Z W c)
  simpa using LinearMap.congr_fun this U

/-- A complex-bilinear form vanishing on real fields is zero. -/
theorem bilinear_ext_of_real
    (T : (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ a b : SignedField, T (signedCoordinates a) (signedCoordinates b) = 0) : T = 0 := by
  have h1 : ∀ Z (b : SignedField), T Z (signedCoordinates b) = 0 := by
    intro Z b
    have := linear_ext_of_real (T.flip (signedCoordinates b)) (fun a => h a b)
    exact LinearMap.congr_fun this Z
  refine LinearMap.ext fun Z => LinearMap.ext fun W => ?_
  have := linear_ext_of_real (T Z) (fun b => h1 Z b)
  simpa using LinearMap.congr_fun this W

end SignedStabilizer

end

end ThirteenPlanes
