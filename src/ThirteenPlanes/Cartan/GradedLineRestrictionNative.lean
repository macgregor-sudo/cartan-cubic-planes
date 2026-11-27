module

public import ThirteenPlanes.Cartan.GradedLineRestrictionSurjective
public import ThirteenPlanes.Cartan.GradedLineRestrictionNativeLift
public import ThirteenPlanes.Cartan.GradeRealAlbertCore

@[expose] public section

set_option backward.privateInPublic true

/-! Real descent for restriction to the actual compact Albert line algebra. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading AlbertGrading.Grading.JC Module

noncomputable section

private def operatorConjugation (D : Module.End ℂ JC) : Module.End ℂ JC where
  toFun x := conj (D (conj x))
  map_add' x y := by rw [conj_add, map_add, conj_add]
  map_smul' c x := by rw [conj_smul, map_smul, conj_smul, star_star]; rfl

private theorem operatorConjugation_apply (D : Module.End ℂ JC) (x : JC) :
    operatorConjugation D x = conj (D (conj x)) := rfl

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex)

local notation "M" => albertGradingBasis hρ
local notation "L" => signedProjectiveLine l
local notation "Q" => lineAlgebraOf ρ l
local notation "K" => NormalizedTernaryBasis.realLineDerivations (albertGradingBasis hρ) (signedProjectiveLine l)

set_option maxHeartbeats 900000 in
private theorem operatorConjugation_mem_grade {D : Module.End ℂ JC} {γ : Charge}
    (hD : D ∈ (M).derivationGrade γ) : operatorConjugation D ∈ (M).derivationGrade (-γ) := by
  obtain ⟨hd, hdeg⟩ := (M).mem_derivationGrade.mp hD
  refine (M).mem_derivationGrade.mpr ⟨?_, ?_⟩
  · intro x y
    have h : D (mul (conj x) (conj y)) =
        mul (D (conj x)) (conj y) + mul (conj x) (D (conj y)) := hd (conj x) (conj y)
    simp only [albertGradingBasis_product, operatorConjugation_apply]
    rw [JC.conj_mul, h, JC.conj_add, JC.conj_mul, JC.conj_mul, JC.conj_conj, JC.conj_conj]
  · intro g
    obtain ⟨c, hc⟩ := hdeg (-g)
    refine ⟨star c, ?_⟩
    rw [operatorConjugation_apply, albertGradingBasis_conj, hc, conj_smul, albertGradingBasis_conj]
    congr 2
    abel

private theorem operatorConjugation_mem_lineDerivations {D : Module.End ℂ JC}
    (hD : D ∈ (M).lineDerivations L) : operatorConjugation D ∈ (M).lineDerivations L := by
  refine Submodule.iSup_induction _ (motive := fun T => operatorConjugation T ∈ (M).lineDerivations L)
    hD ?_ ?_ ?_
  · intro γ T hT
    exact Submodule.mem_iSup_of_mem (-γ) (operatorConjugation_mem_grade hρ hT)
  · have zero : operatorConjugation 0 = 0 := by ext x <;> simp [operatorConjugation_apply, conj_zero]
    rw [zero]
    exact ((M).lineDerivations L).zero_mem
  · intro T U hT hU
    have add : operatorConjugation (T + U) = operatorConjugation T + operatorConjugation U := by
      apply LinearMap.ext
      intro x
      simp only [operatorConjugation_apply, LinearMap.add_apply, conj_add]
    rw [add]
    exact ((M).lineDerivations L).add_mem hT hU

theorem realLineDerivations_preserve_nativeLine {D : Module.End ℝ Glennie.Albert} (hD : D ∈ K) (x : Q) :
    D x.val ∈ Q := by
  have hx := of_mem_gradedLineSubspace_of_mem_lineAlgebra hρ l x.property
  have hy := (M).lineDerivations_preserve_line L ((M).mem_realLineDerivations L |>.mp hD) hx
  rw [mapC_of] at hy
  exact (of_mem_gradedLineSubspace_iff hρ l _).mp hy

/-- Every real derivation of the actual line algebra restricts from a compact Albert derivation
in the sum of the grades of that line. -/
theorem nativeGradedLineRestriction_surjective (B : Module.End ℝ Q)
    (hB : ∀ x y : Q, (B (realLineProduct hρ l x y)).val =
      Glennie.jordan (B x).val y.val + Glennie.jordan x.val (B y).val) :
    ∃ D : albertJordan.skewDerivations, D.val.val ∈ K ∧ ∀ x : Q, (B x).val = D.val.val x.val := by
  let : FiniteDimensional ℂ JC := .of_finrank_pos (by rw [albertGrading_finrank]; decide)
  have ranks (γ : Charge) (hγ : γ ≠ 0) : Module.finrank ℂ ((M).derivationGrade γ) = 2 :=
    (M).derivationGrade_finrank_eq_two (albertGradingDerivations_finrank hρ) hγ
  let Bc : (M).gradedLineDerivations L :=
    ⟨extendGradedLineOperator hρ l B, extendGradedLineOperator_mem_derivations hρ l B hB⟩
  obtain ⟨E, hE⟩ := (M).gradedLineRestriction_surjective L (signedProjectiveLine_finrank l) ranks Bc
  let Ec : ComplexAlbertDerivations :=
    ⟨E.val, mem_complexAlbertDerivations.mpr (by
      have h := (M).lineDerivations_le L E.property
      change (M).IsDerivation E.val at h
      intro x y
      simpa only [albertGradingBasis_product] using h x y)⟩
  let R := complexDerivationRealPart Ec
  have havg : mapC R.val = (1 / 2 : ℂ) • (E.val + operatorConjugation E.val) := by
    apply jc_endomorphism_ext
    intro x
    rw [mapC_of, LinearMap.smul_apply, LinearMap.add_apply, operatorConjugation_apply, conj_of]
    rw [show R.val x = (E.val (of x)).re from rfl, of_re_eq]
  have hR : R.val ∈ K := by
    apply ((M).mem_realLineDerivations L).mpr
    rw [havg]
    exact ((M).lineDerivations L).smul_mem _ (((M).lineDerivations L).add_mem E.property
      (operatorConjugation_mem_lineDerivations hρ l E.property))
  refine ⟨nativeAlbertDerivationSkewEquiv R, hR, ?_⟩
  intro x
  have h := congrArg (fun T : (M).gradedLineDerivations L => (T.val (ofLine hρ l x)).val) hE
  change (((M).gradedLineRestriction L E).val (ofLine hρ l x)).val =
    (extendGradedLineOperator hρ l B (ofLine hρ l x)).val at h
  rw [(M).gradedLineRestriction_apply, extendGradedLineOperator_of] at h
  exact (congrArg JC.re h).symm

end

end ThirteenPlanes.Cartan
