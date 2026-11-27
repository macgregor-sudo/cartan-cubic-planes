module

public import ThirteenPlanes.Cartan.GradedRecutAction
public import ThirteenPlanes.Cartan.GradedRecutGeometry
public import ThirteenPlanes.Cartan.RotatedSplitting

@[expose] public section

/-! The fixed planes and conjugacy class of a rotation along a native projective line. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading

noncomputable section

def recutLinePoints (l : SignedPlaneIndex) : Set SignedPlaneIndex := {p | signedPointOnLine p l}

/-- The family with the four planes on the line conjugated in the compact Albert model. -/
def recutPointPlanes (ρ : TernaryAction) (l : SignedPlaneIndex) (k : Glennie.CompactAutomorphism) :=
  rotatedSummands (pointPlane ρ) (recutLinePoints l) (albertTracelessAction k)

/-- Permuting the four original planes on the chosen line as unlabelled subspaces. -/
def permutesGradedLinePlanes (ρ : TernaryAction) (l : SignedPlaneIndex) (k : Glennie.CompactAutomorphism) : Prop :=
  ∃ σ : Equiv.Perm {p // signedPointOnLine p l}, ∀ p : {p // signedPointOnLine p l},
    (pointPlane ρ p.val).map (albertTracelessAction k).toLinearMap = pointPlane ρ (σ p).val

/-- Rotating a line in an Albert Cartan decomposition with graded fixed planes. -/
theorem recut_decomposition_of_graded_fixedPlanes {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)
    (l : SignedPlaneIndex) (T : SignedPlaneIndex → LieSubalgebra ℝ NativeAlbertDerivations)
    (hT : IsKillingCartanOD T) (fixed : ∀ p, albertRealFixed (T p) = pointPlane ρ p)
    (k : Glennie.CompactAutomorphism)
    (normalizes : (⨆ p : recutLinePoints l, (T p.val).toSubmodule).map (nativeAlbertLieAction k).toLinearMap =
      ⨆ p : recutLinePoints l, (T p.val).toSubmodule) :
    let W := rotatedKillingCartans T (recutLinePoints l) (nativeAlbertLieAction k)
    IsKillingCartanOD W ∧ (∀ p, albertRealFixed (W p) = recutPointPlanes ρ l k p) ∧
      (¬ permutesGradedLinePlanes ρ l k → ¬ ∃ (a : Glennie.CompactAutomorphism) (π : Equiv.Perm SignedPlaneIndex),
        ∀ p, (T p).map (nativeAlbertLieAction a).toLieHom = W (π p)) := by
  classical
  let L := recutLinePoints l
  let W := rotatedKillingCartans T L (nativeAlbertLieAction k)
  have planes (p : SignedPlaneIndex) : albertRealFixed (W p) = recutPointPlanes ρ l k p := by
    change albertRealFixed (rotatedKillingCartans T L (nativeAlbertLieAction k) p) = _
    rw [albertRealFixed_rotated]
    by_cases hp : p ∈ L
    · simp only [recutPointPlanes, rotatedSummands, L, ite_eq_left hp, fixed]
    · simp only [recutPointPlanes, rotatedSummands, L, ite_eq_right hp, fixed]
  refine ⟨rotatedKillingCartans_isOD T hT L (nativeAlbertLieAction k) normalizes, planes, ?_⟩
  rintro hn ⟨a, π, ha⟩
  obtain ⟨σ, hσ⟩ := recutLine_permuted_of_planeConjugacy hρ l (recutPointPlanes ρ l k) (by
    intro p hp
    have hoff : p ∉ recutLinePoints l := hp
    simp only [recutPointPlanes, rotatedSummands, ite_eq_right hoff])
    (albertTracelessAction a) (albertTracelessAction_preserves_cubic a) π (by
      intro p
      rw [← fixed p, ← albertRealFixed_map, ha p]
      exact planes (π p))
  apply hn
  refine ⟨σ, fun p => ?_⟩
  have hon : p.val ∈ recutLinePoints l := p.property
  simpa only [recutPointPlanes, rotatedSummands, ite_eq_left hon] using hσ p

end

end ThirteenPlanes.Cartan
