module

public import ThirteenPlanes.FiniteGroup.Relabel

@[expose] public section

set_option backward.privateInPublic true

/-! Complex coefficient tables of real linear functionals and real trilinear forms on the signed
carrier, in the charge coordinates. -/

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

namespace FiniteGroup

open SignedStabilizer

local notation "z" => signedCoordinates

/-- The coefficient of a real-linear complex functional on the charge coordinate `x`. -/
def fcoef (f : SignedField →ₗ[ℝ] ℂ) (x : NonzeroCharge) : ℂ :=
  (f (testVec x 1) - Complex.I * f (testVec x Complex.I)) / 2

private theorem pair_alg (f1 fI ζ : ℂ) :
    (f1 - Complex.I * fI) / 2 * ζ + (f1 + Complex.I * fI) / 2 * star ζ =
      (ζ.re : ℂ) * f1 + (ζ.im : ℂ) * fI := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Every real-linear complex functional is a complex combination of the charge coordinates. -/
theorem functional_eq_sum (f : SignedField →ₗ[ℝ] ℂ) (u : SignedField) :
    f u = ∑ x, fcoef f x * z u x := by
  set f1 : NonzeroCharge → ℂ := fun x => f (testVec x 1)
  set fI : NonzeroCharge → ℂ := fun x => f (testVec x Complex.I)
  have hg : ∀ x, f (testVec x (z u x)) = ((z u x).re : ℂ) * f1 x + ((z u x).im : ℂ) * fI x := by
    intro x
    rw [testVec_re_im, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hlhs : (2 : ℂ) * f u = ∑ x, f (testVec x (z u x)) := by
    have := congrArg f (two_smul_eq_sum_testVec u)
    rw [map_smul, map_sum, Complex.real_smul] at this
    rw [← this]
    norm_num
  have hf1 : ∀ x, f1 (oppositeCharge x) = f1 x := by
    intro x; simp only [f1, testVec_opposite, star_one]
  have hfI : ∀ x, fI (oppositeCharge x) = -fI x := by
    intro x
    simp only [fI, testVec_opposite, Complex.star_def, Complex.conj_I]
    rw [show testVec x (-Complex.I) = (-1 : ℝ) • testVec x Complex.I by
      rw [testVec_re_im x (-Complex.I)]; simp]
    rw [map_smul, Complex.real_smul]; simp
  have hpair : ∀ x, fcoef f x * z u x + fcoef f (oppositeCharge x) * z u (oppositeCharge x) =
      f (testVec x (z u x)) := by
    intro x
    rw [hg x, signedCoordinates_opposite]
    have hm1 : fcoef f x = (f1 x - Complex.I * fI x) / 2 := rfl
    have hm2 : fcoef f (oppositeCharge x) = (f1 x + Complex.I * fI x) / 2 := by
      change (f1 (oppositeCharge x) - Complex.I * fI (oppositeCharge x)) / 2 = _
      rw [hf1, hfI]; ring
    rw [hm1, hm2]
    exact pair_alg _ _ _
  have hsum : (2 : ℂ) * ∑ x, fcoef f x * z u x = ∑ x, f (testVec x (z u x)) := by
    rw [two_mul]
    conv_lhs => arg 2; rw [← sum_opposite]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hpair x
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) (hlhs.trans hsum.symm)

section Trilinear

variable (f : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ)

private def ofRealL : ℝ →ₗ[ℝ] ℂ := Complex.ofRealCLM.toLinearMap

private def c3 (X Y : SignedField) (k : NonzeroCharge) : ℂ := fcoef (ofRealL ∘ₗ f X Y) k

private def l2 (X : SignedField) (k : NonzeroCharge) : SignedField →ₗ[ℝ] ℂ where
  toFun Y := c3 f X Y k
  map_add' Y Y' := by
    simp only [c3, fcoef, ofRealL, LinearMap.comp_apply, map_add, LinearMap.add_apply,
      ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply]
    ring
  map_smul' r Y := by
    simp only [c3, fcoef, ofRealL, LinearMap.comp_apply, map_smul, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul,
      RingHom.id_apply, Complex.real_smul]
    ring

private def c2 (X : SignedField) (j k : NonzeroCharge) : ℂ := fcoef (l2 f X k) j

private def l1 (j k : NonzeroCharge) : SignedField →ₗ[ℝ] ℂ where
  toFun X := c2 f X j k
  map_add' X X' := by
    simp only [c2, fcoef, l2, c3, ofRealL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      map_add, LinearMap.add_apply, ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply]
    ring
  map_smul' r X := by
    simp only [c2, fcoef, l2, c3, ofRealL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      map_smul, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply,
      smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul]
    ring

/-- The complex coefficient table of a real trilinear form in the charge coordinates. -/
def tableOf (i j k : NonzeroCharge) : ℂ := fcoef (l1 f j k) i

/-- A real trilinear form is the complex trilinear form of its table on real fields. -/
theorem trilinear_eq_triForm (X Y W : SignedField) :
    (f X Y W : ℂ) = triForm (tableOf f) (z X) (z Y) (z W) := by
  rw [triForm_apply]
  have h3 : (f X Y W : ℂ) = ∑ k, c3 f X Y k * z W k := functional_eq_sum (ofRealL ∘ₗ f X Y) W
  have h2 : ∀ k, c3 f X Y k = ∑ j, c2 f X j k * z Y j := fun k => functional_eq_sum (l2 f X k) Y
  have h1 : ∀ j k, c2 f X j k = ∑ i, tableOf f i j k * z X i :=
    fun j k => functional_eq_sum (l1 f j k) X
  rw [h3]
  simp only [h2, h1, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end Trilinear

end FiniteGroup

end

end ThirteenPlanes
