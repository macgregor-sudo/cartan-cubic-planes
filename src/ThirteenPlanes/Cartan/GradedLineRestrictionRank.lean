module

public import ThirteenPlanes.Cartan.GradedLineRestrictionSurjective

@[expose] public section

set_option backward.privateInPublic true

/-! The independent coefficients of derivations of a graded projective line. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

variable {A : Type*} [AddCommGroup A] [Module ℂ A] (M : NormalizedTernaryBasis A)
variable (L : Submodule (ZMod 3) Charge) (hdim : Module.finrank (ZMod 3) L = 2)

local notation "Q" => M.gradedLineSubspace L
local notation "b" => M.gradedLineBasis L
local notation "Deg" => {γ : L // γ ≠ 0}

local instance : Fintype L := Fintype.ofFinite L

private def mateBasis (γ : Deg) : Basis (Fin 2) (ZMod 3) L :=
  (gradedLine_exists_basis L hdim γ.property).choose

private theorem mateBasis_spec (γ : Deg) : mateBasis L hdim γ 0 = γ.val ∧
    IndependentDirections γ.val.val (mateBasis L hdim γ 1).val :=
  (gradedLine_exists_basis L hdim γ.property).choose_spec

/-- For each nonzero degree, record the coefficient in that degree of the action on a
complementary grade of the line. -/
def gradedLineDerivationCoefficients : M.gradedLineDerivations L →ₗ[ℂ] (Deg → ℂ) :=
  LinearMap.pi fun γ => (((b).coord (mateBasis L hdim γ 1 + γ.val)).comp
    (LinearMap.applyₗ (b (mateBasis L hdim γ 1)))).comp (M.gradedLineDerivations L).subtype

private theorem coefficients_apply (D : M.gradedLineDerivations L) (γ : Deg) :
    M.gradedLineDerivationCoefficients L hdim D γ =
      (b).coord (mateBasis L hdim γ 1 + γ.val) (D.val (b (mateBasis L hdim γ 1))) := rfl

theorem gradedLineDerivationCoefficients_injective :
    Function.Injective (M.gradedLineDerivationCoefficients L hdim) := by
  classical
  intro D E he
  let T := D - E
  have hT : M.gradedLineDerivationCoefficients L hdim T = 0 := by
    change M.gradedLineDerivationCoefficients L hdim (D - E) = 0
    rw [(M.gradedLineDerivationCoefficients L hdim).map_sub D E, he, sub_self]
  have hz (γ : L) : M.gradedLineDegreeProjection L γ T.val = 0 := by
    let V := M.gradedLineDegreeProjection L γ T.val
    have hV := M.gradedLineDegreeProjection_derivation L γ T.property
    have hdeg := M.gradedLineDegreeProjection_hasDegree L γ T.val
    by_cases hγ : γ = 0
    · subst γ
      exact M.gradedLineDegree_zero L hV hdeg
    let j : Deg := ⟨γ, hγ⟩
    have hc := congrFun hT j
    rw [M.coefficients_apply L hdim] at hc
    have hscalar : (b).coord (mateBasis L hdim j 1 + γ) (T.val (b (mateBasis L hdim j 1))) = 0 := hc
    obtain ⟨hB, hI⟩ := mateBasis_spec L hdim j
    refine M.gradedLineDerivation_eq_of_basis L (mateBasis L hdim j) hB hI hV
      ((M.gradedLineDerivations L).zero_mem) ?_ ?_
    · exact M.gradedLineDegree_kills_self L hγ hV hdeg
    · rw [LinearMap.zero_apply, M.gradedLineDegreeProjection_on_basis, hscalar, zero_smul]
  have ht := M.gradedLineDegreeProjection_sum L T.val
  simp only [hz, Finset.sum_const_zero] at ht
  apply sub_eq_zero.mp
  exact Subtype.ext ht.symm

include hdim in
private theorem lineNonzeroGrades_card : Fintype.card Deg = 8 := by
  classical
  have hcard := Fintype.card_congr (Module.finBasisOfFinrankEq (R := ZMod 3) (M := L) hdim).equivFun.toEquiv
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard
  change Fintype.card {γ : L // ¬γ = 0} = 8
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]
  norm_num

include hdim in
/-- The degree projections bound all line derivations by the eight nonzero line grades. -/
theorem gradedLineDerivations_finrank_le_eight : Module.finrank ℂ (M.gradedLineDerivations L) ≤ 8 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (M.gradedLineDerivationCoefficients_injective L hdim)
  classical
  rw [Module.finrank_fintype_fun_eq_card, lineNonzeroGrades_card L hdim] at h
  exact h

variable [FiniteDimensional ℂ A]

/-- Each coefficient is realized independently by the restriction of the corresponding
ambient grade. -/
theorem gradedLineDerivationCoefficients_surjective
    (ranks : ∀ γ : Charge, γ ≠ 0 → Module.finrank ℂ (M.derivationGrade γ) = 2) :
    Function.Surjective (M.gradedLineDerivationCoefficients L hdim) := by
  classical
  intro c
  have lift (γ : Deg) : ∃ E : M.derivationGrade γ.val.val,
      M.gradeCoefficient γ.val.val (mateBasis L hdim γ 1).val E.val = c γ := by
    have hI := (mateBasis_spec L hdim γ).2
    obtain ⟨B, hB₀, hB₁⟩ := exists_chargeBasis_extending_two hI
    obtain ⟨E, hE⟩ := (M.gradeEvaluation_bijective B hB₀ (ranks _ hI.left_ne_zero)).surjective (c γ, 0)
    refine ⟨E, ?_⟩
    have h := congrArg Prod.fst hE
    change M.gradeCoefficient γ.val.val (B 1) E.val = c γ at h
    rwa [hB₁] at h
  choose E hE using lift
  let V (γ : Deg) : M.lineDerivations L := ⟨(E γ).val, Submodule.mem_iSup_of_mem γ.val (E γ).property⟩
  let T (γ : Deg) := M.gradedLineRestriction L (V γ)
  refine ⟨∑ γ, T γ, ?_⟩
  funext γ
  rw [map_sum, Finset.sum_apply]
  have hmate (δ : Deg) (hδ : δ ≠ γ) :
      M.gradedLineDerivationCoefficients L hdim (T δ) γ = 0 := by
    rw [M.coefficients_apply L hdim]
    obtain ⟨a, ha⟩ := M.gradedLineRestriction_hasDegree L (E δ).property (mateBasis L hdim γ 1)
    change (T δ).val (b (mateBasis L hdim γ 1)) = _ at ha
    rw [ha, map_smul]
    have hne : mateBasis L hdim γ 1 + γ.val ≠ mateBasis L hdim γ 1 + δ.val :=
      fun h => hδ (Subtype.ext (add_left_cancel h).symm)
    simp [Basis.coord_apply, Basis.repr_self, hne]
  rw [Finset.sum_eq_single γ (fun δ _ hδ => hmate δ hδ) (by simp)]
  rw [M.coefficients_apply L hdim]
  let g : L := mateBasis L hdim γ 1
  have haction : (T γ).val (b g) = c γ • b (g + γ.val) := by
    apply Subtype.ext
    simp only [T, V, M.gradedLineRestriction_apply, M.gradedLineBasis_coe, Submodule.coe_smul,
      Submodule.coe_add]
    rw [M.derivationGrade_apply (E γ).property, hE γ]
  change (b).coord (g + γ.val) ((T γ).val (b g)) = _
  rw [haction, map_smul]
  simp

include hdim in
/-- The rank of restriction and the dimension of the actual line derivations are both eight. -/
theorem gradedLineRestriction_finrank
    (ranks : ∀ γ : Charge, γ ≠ 0 → Module.finrank ℂ (M.derivationGrade γ) = 2) :
    Module.finrank ℂ (M.gradedLineRestriction L).range = 8 ∧
      Module.finrank ℂ (M.gradedLineDerivations L) = 8 := by
  classical
  let e := LinearEquiv.ofBijective (M.gradedLineDerivationCoefficients L hdim)
    ⟨M.gradedLineDerivationCoefficients_injective L hdim,
      M.gradedLineDerivationCoefficients_surjective L hdim ranks⟩
  have h := e.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, lineNonzeroGrades_card L hdim] at h
  refine ⟨?_, h⟩
  rw [LinearMap.range_eq_top.mpr (M.gradedLineRestriction_surjective L hdim ranks), finrank_top, h]

end

end ThirteenPlanes.Cartan.NormalizedTernaryBasis
