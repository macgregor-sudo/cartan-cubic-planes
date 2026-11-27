module

public import ThirteenPlanes.AlbertGrading.Grading.GradedLines

@[expose] public section

set_option backward.privateInPublic true

/-! # ternary grading theorem (The graded system), for every ternary grading group -/

namespace ThirteenPlanes.AlbertGrading

open Grading Grading.JC ThirteenPlanes.RoundCubics ThirteenPlanes.Graded

noncomputable section

private theorem two_points_on_line (l : SignedPlaneIndex) :
    ∃ p q, signedPointOnLine p l ∧ signedPointOnLine q l ∧ p ≠ q := by
  have h : 1 < (signedLinePoints l).card := by rw [signedLinePoints_card]; norm_num
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h
  simp only [signedLinePoints, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  exact ⟨p, q, hp, hq, hpq⟩

private theorem line_through (p q : SignedPlaneIndex) :
    ∃ l, signedPointOnLine p l ∧ signedPointOnLine q l := by
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨q', hq'⟩ := Fintype.exists_ne_of_one_lt_card (by rw [signedPlaneIndex_card]; norm_num) p
    obtain ⟨l, ⟨hp, -⟩, -⟩ := unique_joining_line p q' hq'.symm
    exact ⟨l, hp, hp⟩
  · obtain ⟨l, h, -⟩ := unique_joining_line p q hpq
    exact ⟨l, h⟩

/-- Ternary grading theorem (v): the line algebras. -/
theorem graded_part_five (hQ : FrameProperties.QutritGeneration) {ρ : TernaryAction}
    (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex) :
    (∀ x y, x ∈ lineAlgebraOf ρ l → y ∈ lineAlgebraOf ρ l →
      Glennie.jordan x y ∈ lineAlgebraOf ρ l) ∧
    (∃ I : FullHermitian3 ≃ₗ[ℝ] lineAlgebraOf ρ l, (I hermitianOne).val = 1 ∧
      ∀ X Y, (I (fullHermitianProduct X Y)).val = Glennie.jordan (I X).val (I Y).val) ∧
    (∀ p : SignedPlaneIndex, signedPointOnLine p l → ∀ u ∈ charSpace ρ p.val.val,
      IsNormalized u → ∀ P, IsFrameOf u P → ∀ a, P a ∈ lineAlgebraOf ρ l) ∧
    IsClosedPiece nativeEqualCubic (lineTracelessOf ρ l) := by
  refine ⟨fun x y hx hy => lineAlgebra_closed hρ l hx hy, ?_,
    fun p hp u hu hun P hP a => frame_mem_lineAlgebra hρ hp hu hun hP a,
    lineTraceless_closed hρ l⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := two_points_on_line l
  have hFp := isFrameOf_framePointReal hρ (rep_ne_zero p) (pointUnit_spec hρ p).1
    (pointUnit_spec hρ p).2
  have hFq := isFrameOf_framePointReal hρ (rep_ne_zero q) (pointUnit_spec hρ q).1
    (pointUnit_spec hρ q).2
  have horth : (nativeFramePlane (framePointReal (pointUnit hρ p))).IsOrtho
      (nativeFramePlane (framePointReal (pointUnit hρ q))) := by
    rw [← pointPlane_eq_nativeFramePlane, ← pointPlane_eq_nativeFramePlane]
    exact pointPlane_orthogonal hρ hpq
  obtain ⟨I, h1, hprod⟩ := hQ _ _ hFp.1 hFq.1 horth
  have heq := lineAlgebra_eq_generated hρ hp hq hpq
  refine ⟨I.trans (LinearEquiv.ofEq _ _ heq), ?_, ?_⟩
  · simpa using h1
  · intro X Y
    simpa using hprod X Y

/-- Ternary grading theorem. -/
theorem gradedSystem (hQ : FrameProperties.QutritGeneration) : Statements.GradedSystem := by
  intro ρ hρ
  obtain ⟨i1, i2, i3, i4⟩ := graded_part_one hρ
  refine ⟨i1, i2, i3, i4, graded_part_two hρ, (graded_part_three hρ).1, (graded_part_three hρ).2,
    graded_mixed hρ, graded_share hρ, graded_part_five hQ hρ, line_through⟩

end

end ThirteenPlanes.AlbertGrading
