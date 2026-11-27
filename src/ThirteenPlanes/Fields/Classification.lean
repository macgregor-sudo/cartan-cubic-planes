module

public import ThirteenPlanes.Fields.FieldForm
public import ThirteenPlanes.Peirce.CartanIdentification
public import ThirteenPlanes.Peirce.Count

@[expose] public section

/-! The field count and actual complex and native Albert model identifications. -/

open scoped InnerProductSpace

namespace ThirteenPlanes.Fields

noncomputable section

open Peirce

/-- The exclusion and model clauses of Theorem 6-fields, on the actual field space. -/
theorem classify_radial_threeFieldCubic {m : ℕ} (hm : 1 ≤ m) (h : SymmetricCubic (FieldSpace m))
    (form : HasFieldForm h)
    (radial : ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
      ‖gradient (fun z => h.apply z z z) x‖ = ‖gradient (fun z => h.apply z z z) y‖) :
    m = 1 ∨
    (m = 4 ∧ ∃ I : FieldSpace m ≃ₗᵢ[ℝ] TracelessHermitian3,
      h = complexCartanCubic.pullback I.toLinearMap) ∨
    (m = 13 ∧ ∃ I : FieldSpace m ≃ₗᵢ[ℝ] NativeTraceless,
      h = nativeCartanCubic.pullback I.toLinearMap) := by
  obtain ⟨hr, _, hc⟩ := fieldForm_round_of_radial_gradient hm h form radial
  have hf : 1 ≤ Fintype.card (Fin m) := by simpa using hm
  rcases planeCount_one_four_thirteen hr hc hf with h1 | h4 | h13
  · exact Or.inl (by simpa using h1)
  · obtain ⟨I, hI, _⟩ := closedPlaneSystem_complex hr hc h4 ⟨0, by omega⟩
    exact Or.inr (Or.inl ⟨by simpa using h4, I, hI⟩)
  · obtain ⟨I, hI, _⟩ := closedPlaneSystem_native hr hc h13 ⟨0, by omega⟩
    exact Or.inr (Or.inr ⟨by simpa using h13, I, hI⟩)

end

end ThirteenPlanes.Fields
