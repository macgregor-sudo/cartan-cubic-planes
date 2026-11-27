module

public import ThirteenPlanes.Fields.Polynomial
public import ThirteenPlanes.Fields.Realization

@[expose] public section

/-! Classification and realizations in terms of the prescribed field polynomial. -/

namespace ThirteenPlanes.Fields

noncomputable section

open Peirce

/-- The radiality of the squared norm of the real gradient. -/
def HasRadialFieldEnergy {m : ℕ} (T : IncreasingTriple m → RealTrilinear) : Prop :=
  ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
    ‖gradient (polynomial T) x‖ ^ 2 = ‖gradient (polynomial T) y‖ ^ 2

/-- Theorem 6-fields, with the actual polynomial and literal trace cubes. -/
theorem field_polynomial_count_and_model {m : ℕ} (hm : 1 ≤ m)
    (T : IncreasingTriple m → RealTrilinear) (radial : HasRadialFieldEnergy T) :
    m = 1 ∨
    (m = 4 ∧ ∃ I : FieldSpace m ≃ₗᵢ[ℝ] TracelessHermitian3, ∀ z,
      polynomial T z = Real.sqrt 6 * (Matrix.trace (TracelessHermitian3.toMatrix (I z) ^ 3)).re) ∨
    (m = 13 ∧ ∃ I : FieldSpace m ≃ₗᵢ[ℝ] NativeTraceless, ∀ z,
      polynomial T z = Real.sqrt 6 * Glennie.trace (Glennie.jordan
        (Glennie.jordan (I z : Glennie.Albert) (I z : Glennie.Albert)) (I z : Glennie.Albert))) := by
  have hr : ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
      ‖gradient (fun w => (coefficientCubic T).apply w w w) x‖ =
      ‖gradient (fun w => (coefficientCubic T).apply w w w) y‖ := by
    intro x y hxy
    simp only [coefficientCubic_diagonal]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (radial x y hxy)
  rcases classify_radial_threeFieldCubic hm _ ⟨T, coefficientCubic_diagonal T⟩ hr with h1 | ⟨h4, I, hI⟩ | ⟨h13, I, hI⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨h4, I, fun z => ?_⟩)
    rw [← coefficientCubic_diagonal, hI, SymmetricCubic.pullback_apply, complexCartanCubic_diagonal]
    rfl
  · refine Or.inr (Or.inr ⟨h13, I, fun z => ?_⟩)
    rw [← coefficientCubic_diagonal, hI, SymmetricCubic.pullback_apply, nativeCartanCubic_apply]
    rfl

/-- Both proper field counts occur for genuine coefficient families with radial energy. -/
theorem four_and_thirteen_radial_field_polynomials :
    (∃ T : IncreasingTriple 4 → RealTrilinear, HasRadialFieldEnergy T) ∧
      (∃ T : IncreasingTriple 13 → RealTrilinear, HasRadialFieldEnergy T) := by
  have witness (m : ℕ) (hw : ∃ h : SymmetricCubic (FieldSpace m), HasFieldForm h ∧ IsRound h 1) :
      ∃ T : IncreasingTriple m → RealTrilinear, HasRadialFieldEnergy T := by
    obtain ⟨h, ⟨T, hT⟩, round⟩ := hw
    refine ⟨T, fun x y hxy => ?_⟩
    have hr := radial_gradient_of_round round x y hxy
    simp only [hT] at hr
    rw [hr]
  exact ⟨witness 4 four_and_thirteen_field_realizations.1, witness 13 four_and_thirteen_field_realizations.2⟩

end

end ThirteenPlanes.Fields
