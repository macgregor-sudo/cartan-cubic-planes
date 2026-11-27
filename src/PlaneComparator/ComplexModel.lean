/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CubicPlaneDefs
public import ThirteenPlanes.Peirce.SlotComplexModel

@[expose] public section

set_option backward.privateInPublic true

/-! Literal coordinate and trace-pairing comparisons for the complex Cartan model. -/

open scoped BigOperators InnerProductSpace

namespace Challenge.Bridge

open ThirteenPlanes

noncomputable section

private def toComplexModel : ThirteenPlanes.TracelessHermitian3 →ₗ[ℝ] TracelessComplexHermitian3 where
  toFun x := ⟨⟨ThirteenPlanes.TracelessHermitian3.toMatrix x, x.isHermitian⟩, x.trace_eq_zero⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def complexModel : ThirteenPlanes.TracelessHermitian3 ≃ₗ[ℝ] TracelessComplexHermitian3 :=
  LinearEquiv.ofBijective toComplexModel ⟨fun _ _ eq =>
    ThirteenPlanes.TracelessHermitian3.toMatrix_injective
      (congrArg complexMatrix eq), fun x => by
    refine ⟨ThirteenPlanes.TracelessHermitian3.ofMatrix (complexMatrix x) x.val.property x.property, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl⟩

@[simp] theorem complexModel_matrix (x : ThirteenPlanes.TracelessHermitian3) :
    complexMatrix (complexModel x) = ThirteenPlanes.TracelessHermitian3.toMatrix x := rfl

theorem complexModel_tracePairing (x y : ThirteenPlanes.TracelessHermitian3) :
    (Matrix.trace (complexMatrix (complexModel x) * complexMatrix (complexModel y))).re =
      ⟪x, y⟫_ℝ := (x.inner_eq_tracePairing y).symm

theorem isometry_preserves_inner
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (I : V ≃ₗᵢ[ℝ] W) (x y : V) : ⟪I x, I y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have h := norm_add_sq_real (I x) (I y)
  rw [← I.map_add, I.norm_map, I.norm_map, I.norm_map] at h
  nlinarith only [h, norm_add_sq_real x y]

theorem complex_form_of_cubic {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (h : SymmetricCubic V) {c : ℝ}
    (K : V ≃ₗᵢ[ℝ] ThirteenPlanes.TracelessHermitian3)
    (heq : h = Real.sqrt c • Peirce.complexCartanCubic.pullback K.toLinearMap) :
    ComplexCartanForm (fun x : V => h.apply x x x) (Real.sqrt (6 * c)) := by
  refine ⟨K.toLinearEquiv.trans complexModel, ?_, ?_⟩
  · intro x y
    change ⟪x, y⟫_ℝ = (Matrix.trace
      (complexMatrix (complexModel (K x)) * complexMatrix (complexModel (K y)))).re
    rw [complexModel_tracePairing]
    have hm := norm_add_sq_real (K x) (K y)
    rw [← K.map_add, K.norm_map, K.norm_map, K.norm_map] at hm
    nlinarith only [hm, norm_add_sq_real x y]
  · intro x
    change h.apply x x x = Real.sqrt (6 * c) *
      (Matrix.trace (complexMatrix (complexModel (K x)) ^ 3)).re
    rw [heq, SymmetricCubic.apply_smul, SymmetricCubic.pullback_apply, Peirce.complexCartanCubic_diagonal,
      complexModel_matrix, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
    let tr := (Matrix.trace (ThirteenPlanes.TracelessHermitian3.toMatrix (K x) ^ 3)).re
    change Real.sqrt c * (Real.sqrt 6 * tr) = (Real.sqrt 6 * Real.sqrt c) * tr
    ring

end

end Challenge.Bridge
