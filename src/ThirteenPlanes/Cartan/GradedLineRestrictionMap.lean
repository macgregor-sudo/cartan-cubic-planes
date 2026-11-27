module

public import ThirteenPlanes.Cartan.GradedLineRestrictionNative
public import ThirteenPlanes.Cartan.GradedLineRestrictionRank

@[expose] public section

set_option backward.privateInPublic true

/-! Restriction as a surjective real linear map between the actual derivation spaces. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading AlbertGrading.Grading.JC Module

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex)

local notation "Q" => lineAlgebraOf ρ l
local notation "K" => NormalizedTernaryBasis.realLineDerivations (albertGradingBasis hρ) (signedProjectiveLine l)

set_option maxHeartbeats 950000 in
/-- The literal real Albert product, with both arguments and values in the graded line. -/
def realGradedLineProductLinear : Q →ₗ[ℝ] Q →ₗ[ℝ] Q :=
  LinearMap.mk₂ ℝ (realLineProduct hρ l)
    (fun x y z => Subtype.ext (Glennie.jordan_add_left x.val y.val z.val))
    (fun r x y => Subtype.ext (Glennie.jordan_smul_left r x.val y.val))
    (fun x y z => Subtype.ext (Glennie.jordan_add_right x.val y.val z.val))
    (fun r x y => Subtype.ext (Glennie.jordan_smul_right r x.val y.val))

/-- All real derivations of the actual line algebra. -/
def nativeGradedLineDerivations : Submodule ℝ (Module.End ℝ Q) :=
  (productDerivations (realGradedLineProductLinear hρ l)).toSubmodule

theorem mem_nativeGradedLineDerivations {B : Module.End ℝ Q} : B ∈ nativeGradedLineDerivations hρ l ↔
    ∀ x y : Q, (B (realLineProduct hρ l x y)).val =
      Glennie.jordan (B x).val y.val + Glennie.jordan x.val (B y).val := by
  constructor
  · intro h x y
    exact congrArg Subtype.val (h x y)
  · intro h x y
    exact Subtype.ext (h x y)

private def realGradedLineRestrictionValue (D : K) : Module.End ℝ Q :=
  (D.val.comp (Q).subtype).codRestrict Q (fun x => realLineDerivations_preserve_nativeLine hρ l D.property x)

/-- Restriction from the sum of the compact Albert grades on a projective line. -/
def nativeGradedLineRestriction : K →ₗ[ℝ] nativeGradedLineDerivations hρ l where
  toFun D := ⟨realGradedLineRestrictionValue hρ l D, (mem_nativeGradedLineDerivations hρ l).mpr (by
    intro x y
    have hder := (albertGradingBasis hρ).lineDerivations_le (signedProjectiveLine l)
      ((albertGradingBasis hρ).mem_realLineDerivations (signedProjectiveLine l) |>.mp D.property)
    change (albertGradingBasis hρ).IsDerivation (mapC D.val) at hder
    have h := hder (of x.val) (of y.val)
    simp only [albertGradingBasis_product, of_mul, mapC_of] at h
    exact congrArg re h)⟩
  map_add' D E := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  map_smul' r D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl

@[simp] theorem nativeGradedLineRestriction_apply (D : K) (x : Q) :
    ((nativeGradedLineRestriction hρ l D).val x).val = D.val x.val := rfl

/-- Restriction is onto all derivations of the literal real grade-line algebra. -/
theorem nativeGradedLineRestriction_onto : Function.Surjective (nativeGradedLineRestriction hρ l) := by
  intro B
  obtain ⟨D, hD, h⟩ := nativeGradedLineRestriction_surjective hρ l B.val
    ((mem_nativeGradedLineDerivations hρ l).mp B.property)
  refine ⟨⟨D.val.val, hD⟩, Subtype.ext (LinearMap.ext fun x => Subtype.ext ?_)⟩
  rw [nativeGradedLineRestriction_apply]
  exact (h x).symm

/-- For the actual native grading, the complex restriction image and all complex line derivations
both have dimension eight. -/
theorem nativeGradedLineRestriction_complex_finrank :
    Module.finrank ℂ ((albertGradingBasis hρ).gradedLineRestriction (signedProjectiveLine l)).range = 8 ∧
      Module.finrank ℂ ((albertGradingBasis hρ).gradedLineDerivations (signedProjectiveLine l)) = 8 := by
  let : FiniteDimensional ℂ JC := .of_finrank_pos (by rw [albertGrading_finrank]; decide)
  exact (albertGradingBasis hρ).gradedLineRestriction_finrank (signedProjectiveLine l)
    (signedProjectiveLine_finrank l) (fun γ hγ =>
      (albertGradingBasis hρ).derivationGrade_finrank_eq_two (albertGradingDerivations_finrank hρ) hγ)

end

end ThirteenPlanes.Cartan
