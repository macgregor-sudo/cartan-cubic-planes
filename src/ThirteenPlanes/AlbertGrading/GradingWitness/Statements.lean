module

public import ThirteenPlanes.AlbertGrading.Grading.Statements

@[expose] public section

/-! The reference grading of the native Albert algebra.

The action `Graded.nativeGradingHom` of `𝔽₃³` supplies the hypotheses for the graded-system
theorem and its phase obstruction. -/

namespace ThirteenPlanes.AlbertGrading

open Grading Grading.JC ThirteenPlanes.RoundCubics ThirteenPlanes.Graded

noncomputable section

/-- The accepted reference action `Graded.nativeGradingHom`. -/
local notation "ρ₀" => Graded.nativeGradingHom

/-- The accepted reference action is a ternary grading group: injective, by Jordan
automorphisms, with every character space of `J_ℂ` one-dimensional. -/
def Statements.ReferenceTernaryGrading : Prop := IsTernaryGrading ρ₀

/-- Some ternary grading group exists (the hypothesis of the ternary grading theorem, complex phases of graded plane coefficients is
satisfiable). -/
def Statements.TernaryGradingExists : Prop := ∃ ρ : TernaryAction, IsTernaryGrading ρ

/-- Ternary grading theorem, all five clauses, for the reference grading. -/
def Statements.GradedSystemNative : Prop :=
  -- (i)
  (charSpace ρ₀ 0 = Submodule.span ℂ {one}) ∧
  (∀ g z, z ∈ charSpace ρ₀ g → conj z ∈ charSpace ρ₀ (-g)) ∧
  (∀ g h z w, z ∈ charSpace ρ₀ g → w ∈ charSpace ρ₀ h → mul z w ∈ charSpace ρ₀ (g + h)) ∧
  (∀ g h z w, z ∈ charSpace ρ₀ g → w ∈ charSpace ρ₀ h → g + h ≠ 0 → ip z w = 0) ∧
  -- (ii)
  (∀ g : Charge, g ≠ 0 →
    (∃ u ∈ charSpace ρ₀ g, IsNormalized u) ∧
    (∀ u ∈ charSpace ρ₀ g, IsNormalized u → ∀ v ∈ charSpace ρ₀ g, IsNormalized v →
      ∃ a : ZMod 3, v = chargePhase a • u) ∧
    (∀ u ∈ charSpace ρ₀ g, IsNormalized u →
      ∃ p : Fin 3 → Glennie.Albert, IsFrameOf u p ∧ contrast p = u ∧
        nativeFramePlane p = gradedPlane ρ₀ g ∧ gradedPlaneJ ρ₀ g ≤ Glennie.traceLinear.ker)) ∧
  -- (iii)
  (∀ (u : Charge → JC) (P : Charge → Fin 3 → Glennie.Albert),
    (∀ g, g ≠ 0 → u g ∈ charSpace ρ₀ g ∧ IsNormalized (u g) ∧ IsFrameOf (u g) (P g)) →
    ∀ g h, g ≠ 0 → h ≠ 0 → h ≠ g → h ≠ -g → ∀ a b, Glennie.inner (P g a) (P h b) = 1 / 3) ∧
  (⨆ p : SignedPlaneIndex, pointPlane ρ₀ p) = ⊤ ∧
  -- (iv)
  (∀ p q r r' : SignedPlaneIndex, p ≠ q → r ≠ r' → r ≠ p → r ≠ q → r' ≠ p → r' ≠ q →
    signedCollinear p q r → signedCollinear p q r' →
    mixedProductSpace nativeEqualCubic (pointPlane ρ₀ p) (pointPlane ρ₀ q) =
      pointPlane ρ₀ r ⊔ pointPlane ρ₀ r') ∧
  (∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r →
    shareOfThreePlanes nativeEqualCubic (pointPlane ρ₀ p) (pointPlane ρ₀ q) (pointPlane ρ₀ r) =
      if signedCollinear p q r then 1 else 0) ∧
  -- (v)
  (∀ l : SignedPlaneIndex,
    (∀ x y, x ∈ lineAlgebraOf ρ₀ l → y ∈ lineAlgebraOf ρ₀ l →
      Glennie.jordan x y ∈ lineAlgebraOf ρ₀ l) ∧
    (∃ I : FullHermitian3 ≃ₗ[ℝ] lineAlgebraOf ρ₀ l, (I hermitianOne).val = 1 ∧
      ∀ X Y, (I (fullHermitianProduct X Y)).val = Glennie.jordan (I X).val (I Y).val) ∧
    (∀ p : SignedPlaneIndex, signedPointOnLine p l → ∀ u ∈ charSpace ρ₀ p.val.val,
      IsNormalized u → ∀ P, IsFrameOf u P → ∀ a, P a ∈ lineAlgebraOf ρ₀ l) ∧
    IsClosedPiece nativeEqualCubic (lineTracelessOf ρ₀ l)) ∧
  (∀ p q : SignedPlaneIndex, ∃ l, signedPointOnLine p l ∧ signedPointOnLine q l)

/-- Complex phases of graded plane coefficients for the reference grading. -/
def Statements.NoRealPlaneCoordinatesNative : Prop :=
  ∀ ψ : SignedPlaneIndex → (ℂ →ₗ[ℝ] NativeTraceless),
    (∀ p ζ, ψ p ζ ∈ pointPlane ρ₀ p) →
    (∀ ζ : SignedPlaneIndex → ℂ, ‖∑ p, ψ p (ζ p)‖ ^ 2 = ∑ p, ‖ζ p‖ ^ 2) →
    (∀ p ζ, Real.sqrt 6 * nativeEqualCubic.apply (ψ p ζ) (ψ p ζ) (ψ p ζ) = (ζ ^ 3).re) →
    ¬ (∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r → ∀ ζ₁ ζ₂ ζ₃ : ℂ,
        nativeEqualCubic.apply (ψ p (star ζ₁)) (ψ q (star ζ₂)) (ψ r (star ζ₃)) =
          nativeEqualCubic.apply (ψ p ζ₁) (ψ q ζ₂) (ψ r ζ₃))

end

end ThirteenPlanes.AlbertGrading
