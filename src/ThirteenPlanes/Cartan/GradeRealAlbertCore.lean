module

public import ThirteenPlanes.Cartan.AlbertDerivationComplex
public import ThirteenPlanes.Cartan.AlbertGradingBasis
public import ThirteenPlanes.Cartan.DerivationGradingTrace
public import ThirteenPlanes.Cartan.GradeRealGrouping
public import ThirteenPlanes.Cartan.GradeRealKilling

@[expose] public section

/-! The complex grades on the complexified native compact Albert derivation algebra. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading LieAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The faithful complexified native action on the literal complex Albert matrices. -/
def albertGradingRep : LieComplex NativeAlbertDerivations →ₗ[ℂ] Module.End ℂ JC :=
  complexAlbertDerivations.toSubmodule.subtype.comp albertDerivationComplexEquiv.toLinearEquiv.toLinearMap

theorem albertGradingRep_injective : Function.Injective albertGradingRep :=
  Subtype.val_injective.comp albertDerivationComplexEquiv.injective

theorem albertGradingRep_map_lie (X Y : LieComplex NativeAlbertDerivations) :
    albertGradingRep ⁅X, Y⁆ = operatorBracket (albertGradingRep X) (albertGradingRep Y) := by
  exact congrArg (fun D : ComplexAlbertDerivations => D.val) (albertDerivationComplexEquiv.map_lie X Y)

@[simp] theorem albertGradingRep_ofReal (D : NativeAlbertDerivations) (x : Glennie.Albert) :
    albertGradingRep (LieComplex.ofReal D) (JC.of x) = JC.of (D.val x) := by
  change (albertDerivationComplexEquiv (LieComplex.ofReal D)).val (JC.of x) = _
  rw [albertDerivationComplexEquiv_apply_ofReal, extendAlbertDerivation_val]
  exact JC.mapC_of _ _

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)

theorem albertGradingRep_range : albertGradingRep.range = (albertGradingBasis hρ).derivations := by
  have hr : albertDerivationComplexEquiv.toLinearEquiv.toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr albertDerivationComplexEquiv.toLinearEquiv.surjective
  unfold albertGradingRep
  rw [LinearMap.range_comp, hr, Submodule.map_subtype_top]
  apply Submodule.ext
  intro D
  change D ∈ complexAlbertDerivations ↔ D ∈ (albertGradingBasis hρ).derivations
  simp only [mem_complexAlbertDerivations, NormalizedTernaryBasis.mem_derivations,
    NormalizedTernaryBasis.IsDerivation, albertGradingBasis_product]

theorem albertGradingDerivations_finrank :
    Module.finrank ℂ (albertGradingBasis hρ).derivations = 52 := by
  rw [← albertGradingRep_range hρ, LinearMap.finrank_range_of_inj albertGradingRep_injective]
  exact albertDerivationComplexEquiv.toLinearEquiv.finrank_eq.trans complexAlbertDerivations_finrank

/-- A complex degree space in the scalar extension of the actual real derivation Lie algebra. -/
def albertComplexGrade (γ : Charge) : Submodule ℂ (LieComplex NativeAlbertDerivations) :=
  ((albertGradingBasis hρ).derivationGrade γ).comap albertGradingRep

theorem albertComplexGrade_map (γ : Charge) :
    (albertComplexGrade hρ γ).map albertGradingRep = (albertGradingBasis hρ).derivationGrade γ := by
  apply Submodule.map_comap_eq_of_le
  rw [albertGradingRep_range hρ, ← (albertGradingBasis hρ).derivationGrades_iSup_eq]
  exact le_iSup _ γ

theorem albertComplexGrades_isInternal : DirectSum.IsInternal (albertComplexGrade hρ) := by
  apply isInternal_comap_of_range _ _ albertGradingRep_injective
    (albertGradingBasis hρ).derivationGrades_independent
  rw [(albertGradingBasis hρ).derivationGrades_iSup_eq, albertGradingRep_range hρ]

theorem albertComplexGrade_zero : albertComplexGrade hρ 0 = ⊥ := by
  rw [albertComplexGrade, NormalizedTernaryBasis.derivationGrade_zero_eq_bot, Submodule.comap_bot,
    LinearMap.ker_eq_bot.mpr albertGradingRep_injective]

theorem albertComplexGrade_finrank {γ : Charge} (hγ : γ ≠ 0) :
    Module.finrank ℂ (albertComplexGrade hρ γ) = 2 := by
  let : Module.Finite ℂ JC := Module.Finite.of_basis (albertGradingBasis hρ).basis
  have h := ((albertComplexGrade hρ γ).equivMapOfInjective albertGradingRep
    albertGradingRep_injective).finrank_eq
  rw [albertComplexGrade_map hρ γ] at h
  exact h.trans ((albertGradingBasis hρ).derivationGrade_finrank_eq_two
    (albertGradingDerivations_finrank hρ) hγ)

theorem albertComplexGrade_lie (g h : Charge) (X Y : LieComplex NativeAlbertDerivations)
    (hx : X ∈ albertComplexGrade hρ g) (hy : Y ∈ albertComplexGrade hρ h) :
    ⁅X, Y⁆ ∈ albertComplexGrade hρ (g + h) := by
  change albertGradingRep ⁅X, Y⁆ ∈ (albertGradingBasis hρ).derivationGrade (g + h)
  rw [albertGradingRep_map_lie]
  exact (albertGradingBasis hρ).derivationGrade_bracket hx hy

theorem albertComplexGradePair_map (p : SignedPlaneIndex) :
    ((pairedGrade (albertComplexGrade hρ) p).map albertGradingRep) =
      (albertGradingBasis hρ).gradePair p.val.val := by
  rw [pairedGrade, Submodule.map_sup, albertComplexGrade_map hρ, albertComplexGrade_map hρ]
  rfl

theorem albertComplexGradePair_mem (p : SignedPlaneIndex) (X : LieComplex NativeAlbertDerivations) :
    X ∈ pairedGrade (albertComplexGrade hρ) p ↔
      albertGradingRep X ∈ (albertGradingBasis hρ).gradePair p.val.val := by
  rw [← albertComplexGradePair_map]
  constructor
  · exact Submodule.mem_map_of_mem
  · rintro ⟨Y, hY, he⟩
    exact albertGradingRep_injective he ▸ hY

theorem albertComplexGradePair_finrank (p : SignedPlaneIndex) :
    Module.finrank ℂ (pairedGrade (albertComplexGrade hρ) p) = 4 := by
  rw [pairedGrade_finrank _ (albertComplexGrades_isInternal hρ).submodule_iSupIndep,
    albertComplexGrade_finrank hρ p.val.property,
    albertComplexGrade_finrank hρ (neg_ne_zero.mpr p.val.property)]

theorem albertComplexGradePairs_killing_orthogonal :
    Pairwise fun p q : SignedPlaneIndex =>
      ∀ X ∈ pairedGrade (albertComplexGrade hρ) p, ∀ Y ∈ pairedGrade (albertComplexGrade hρ) q,
      killingForm ℂ (LieComplex NativeAlbertDerivations) X Y = 0 := by
  intro p q hpq X hX Y hY
  have hne := representatives_not_eq_or_neg hpq
  exact killing_orthogonal_gradePairs _ (albertComplexGrades_isInternal hρ)
    (albertComplexGrade_lie hρ) hne.1 hne.2 hX hY

end

end ThirteenPlanes.Cartan
