module

public import ThirteenPlanes.Cartan.AlbertGradingNonzero
public import ThirteenPlanes.AlbertGrading.Grading.Normalization
public import ThirteenPlanes.SignedPlanes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true

/-! A normalized basis chosen from the actual character lines of any native ternary grading. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading AlbertGrading.Grading.JC Module
open scoped BigOperators

noncomputable section

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)

private def representativeVector (g : Charge) (hg : g ≠ 0) : JC :=
  (exists_normalized hρ hg).choose

private theorem representativeVector_spec (g : Charge) (hg : g ≠ 0) :
    representativeVector hρ g hg ∈ charSpace ρ g ∧ IsNormalized (representativeVector hρ g hg) :=
  (exists_normalized hρ hg).choose_spec

private theorem rep_neg_iff (g : Charge) (hg : g ≠ 0) :
    isChargeRepresentative (-g) ↔ ¬isChargeRepresentative g :=
  oppositeCharge_isRepresentative_iff ⟨g, hg⟩

private def gradingVector (g : Charge) : JC :=
  if hg : g = 0 then one
  else if isChargeRepresentative g then representativeVector hρ g hg
  else conj (representativeVector hρ (-g) (neg_ne_zero.mpr hg))

@[simp] private theorem gradingVector_zero : gradingVector hρ 0 = one := by simp [gradingVector]

private theorem gradingVector_conj (g : Charge) : conj (gradingVector hρ g) = gradingVector hρ (-g) := by
  by_cases hg : g = 0
  · subst g
    simp [one, conj, of]
  have hn := neg_ne_zero.mpr hg
  by_cases hrep : isChargeRepresentative g
  · have hneg : ¬ isChargeRepresentative (-g) := fun h => (rep_neg_iff g hg).mp h hrep
    simp [gradingVector, hg, hn, hrep, hneg, neg_neg]
  · have hneg := (rep_neg_iff g hg).mpr hrep
    simp [gradingVector, hg, hn, hrep, hneg]

private theorem gradingVector_mem (g : Charge) : gradingVector hρ g ∈ charSpace ρ g := by
  by_cases hg : g = 0
  · subst g
    simpa only [gradingVector_zero] using one_mem_charSpace_zero hρ
  by_cases hrep : isChargeRepresentative g
  · simpa only [gradingVector, dite_eq_right hg, ite_eq_left hrep] using (representativeVector_spec hρ g hg).1
  · simpa only [gradingVector, dite_eq_right hg, ite_eq_right hrep, neg_neg] using
      conj_mem_charSpace (representativeVector_spec hρ (-g) (neg_ne_zero.mpr hg)).1

private theorem conjugate_normalized {z : JC} (hz : IsNormalized z) : IsNormalized (conj z) := by
  constructor
  · simpa only [conj_conj] using conj_mul_conj_of_normalized hz
  · rw [conj_conj, JC.mul_comm (conj z) z, hz.2]

private theorem gradingVector_normalized (g : Charge) : IsNormalized (gradingVector hρ g) := by
  by_cases hg : g = 0
  · subst g
    rw [gradingVector_zero]
    have h : conj one = one := by apply JC.ext <;> simp [one, conj]
    exact ⟨by rw [one_mul, h], one_mul _ |>.trans h⟩
  by_cases hrep : isChargeRepresentative g
  · simpa only [gradingVector, dite_eq_right hg, ite_eq_left hrep] using (representativeVector_spec hρ g hg).2
  · simpa only [gradingVector, dite_eq_right hg, ite_eq_right hrep] using
      conjugate_normalized (representativeVector_spec hρ (-g) (neg_ne_zero.mpr hg)).2

private def ipLeftLinear (z : JC) : JC →ₗ[ℂ] ℂ where
  toFun x := ip x z
  map_add' x y := ip_add_left x y z
  map_smul' c x := ip_smul_left c x z

private theorem gradingVector_li : LinearIndependent ℂ (gradingVector hρ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  let f := ipLeftLinear (conj (gradingVector hρ j))
  have hf := congrArg f ha
  rw [map_sum, map_zero] at hf
  simp only [map_smul, smul_eq_mul] at hf
  have hdiag : f (gradingVector hρ j) = 3 := normalized_opposite_ip (gradingVector_normalized hρ j)
  have hzero (i : Charge) (hij : i ≠ j) : f (gradingVector hρ i) = 0 :=
    ip_eq_zero_of_charSpace hρ (gradingVector_mem hρ i) (conj_mem_charSpace (gradingVector_mem hρ j))
      (by simpa only [sub_eq_add_neg] using sub_ne_zero.mpr hij)
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hzero i hij, mul_zero]) (by simp), hdiag] at hf
  exact (mul_eq_zero.mp hf).resolve_right (by norm_num)

private def gradingRealEquiv : JC ≃ₗ[ℝ] Glennie.Albert × Glennie.Albert :=
  { JC.toProd with
    map_add' := fun _ _ => rfl
    map_smul' := fun r z => Prod.ext (JC.real_smul_re r z) (JC.real_smul_im r z) }

/-- The actual complexified Albert carrier has dimension 27 over the complexes. -/
theorem albertGrading_finrank : Module.finrank ℂ JC = 27 := by
  have h := gradingRealEquiv.finrank_eq
  rw [finrank_real_of_complex, Module.finrank_prod, Glennie.albert_finrank] at h
  omega

private def gradingBasis : Basis Charge ℂ JC :=
  basisOfLinearIndependentOfCardEqFinrank (gradingVector_li hρ) (by
    rw [albertGrading_finrank]
    decide)

@[simp] private theorem gradingBasis_apply (g : Charge) : gradingBasis hρ g = gradingVector hρ g := by
  unfold gradingBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The actual polarized Jordan product on the complexified Albert carrier. -/
def albertGradingProduct : JC →ₗ[ℂ] JC →ₗ[ℂ] JC :=
  LinearMap.mk₂ ℂ mul mul_add_left mul_smul_left mul_add_right mul_smul_right

@[simp] theorem albertGradingProduct_apply (x y : JC) : albertGradingProduct x y = mul x y := rfl

/-- Every actual native ternary grading provides a normalized basis with nonzero independent products. -/
def albertGradingBasis : NormalizedTernaryBasis JC where
  basis := gradingBasis hρ
  product := albertGradingProduct
  unit_left x := by simp only [gradingBasis_apply, gradingVector_zero, albertGradingProduct_apply, JC.one_mul]
  comm x y := JC.mul_comm x y
  homogeneous_product g h := by
    simp only [albertGradingProduct_apply, gradingBasis_apply]
    have hg := gradingVector_mem hρ g
    have hh := gradingVector_mem hρ h
    have hn := ne_zero_of_normalized (gradingVector_normalized hρ (g + h))
    exact exists_smul_of_mem hρ (gradingVector_mem hρ (g + h)) hn (mul_mem_charSpace hρ hg hh)
  square g _ := by
    simp only [albertGradingProduct_apply, gradingBasis_apply]
    rw [(gradingVector_normalized hρ g).1, gradingVector_conj]
  opposite g _ := by
    simp only [albertGradingProduct_apply, gradingBasis_apply, gradingVector_zero, ← gradingVector_conj hρ g]
    exact (gradingVector_normalized hρ g).2
  independent_product g h hg hh hne hopp := by
    simp only [albertGradingProduct_apply, gradingBasis_apply]
    exact albert_normalized_independent_product hρ hg hh hne hopp (gradingVector_mem hρ g)
      (gradingVector_mem hρ h) (gradingVector_normalized hρ g) (gradingVector_normalized hρ h)

@[simp] theorem albertGradingBasis_unit : (albertGradingBasis hρ).basis 0 = one := by
  change gradingBasis hρ 0 = one
  rw [gradingBasis_apply, gradingVector_zero]

@[simp] theorem albertGradingBasis_product (x y : JC) :
    (albertGradingBasis hρ).product x y = mul x y := rfl

/-- Membership in the original eigenline of the actual grading action. -/
theorem albertGradingBasis_mem_charSpace (g : Charge) :
    (albertGradingBasis hρ).basis g ∈ charSpace ρ g := by
  change gradingBasis hρ g ∈ charSpace ρ g
  rw [gradingBasis_apply]
  exact gradingVector_mem hρ g

/-- The native real conjugation pairs the two chosen opposite character vectors. -/
theorem albertGradingBasis_conj (g : Charge) :
    conj ((albertGradingBasis hρ).basis g) = (albertGradingBasis hρ).basis (-g) := by
  change conj (gradingBasis hρ g) = gradingBasis hρ (-g)
  rw [gradingBasis_apply, gradingBasis_apply, gradingVector_conj]

end

end ThirteenPlanes.Cartan
