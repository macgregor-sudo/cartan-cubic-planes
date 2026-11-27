module

public import ThirteenPlanes.AlbertGrading.Cubic.GradedCubic
public import ThirteenPlanes.AlbertGrading.Cubic.TitsCubic

@[expose] public section

/-! # graded cubic expansion, every clause: `Targets.ThirteenPlaneCubicFull` -/

open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

open Grading Tits Cubic

noncomputable section

/-- `(thirteen-field polynomial)` in `J_T` with the explicit exponents `φ_{ghk} = [v,w](l−k')`. -/
theorem titsThirteenPlaneCubic (sgn : SignedPlaneIndex → Bool) (ζ : SignedPlaneIndex → ℂ)
    (X : CompactTits)
    (hX : CompactTits.coordinates X = ((Real.sqrt 6)⁻¹ : ℂ) •
      ∑ p, (ζ p • titsBasis (signedGrade p (sgn p)).val +
        star (ζ p) • titsBasis (-(signedGrade p (sgn p)).val))) :
    (∀ t ∈ signedCollinearTriples, ∀ x ∈ tripleReps t, titsTerm sgn ζ x = titsValue sgn ζ t) ∧
    Real.sqrt 6 * (titsTraceForm (CompactTits.coordinates (CompactTits.product X X))
        (CompactTits.coordinates X)).re =
      ∑ p, (ζ p ^ 3).re - 3 * ∑ t ∈ signedCollinearTriples, titsValue sgn ζ t := by
  have hD := titsCoeff_data sgn ζ
  refine ⟨fun t ht x hx => ?_, ?_⟩
  · have hm := mem_repsF.mpr hx
    obtain ⟨p1, -, -⟩ := proper_of_mem_reps ht hm
    have hm' := hm
    rw [repsF, Finset.mem_filter] at hm'
    rw [titsTerm_eq_tT sgn ζ hm'.2.1 (ne_of_point_ne p1), titsValue_eq_tV sgn ζ ht,
      tT_eq_tV hD ht hx]
  have hXs : CompactTits.coordinates X = (((Real.sqrt 6)⁻¹ : ℝ) : ℂ) •
      ∑ k, gradeCoord sgn ζ k • titsBasis k.val := by
    rw [hX, sum_field_tits]; push_cast; rfl
  rw [ThirteenPlanes.AlbertGrading.coordinates_product, hXs, tf_pp_sum]
  have hfs : (∑ x : Triple, titsTraceForm (firstTitsJordanProduct (titsBasis x.1.val) (titsBasis x.2.1.val))
      (titsBasis x.2.2.val) * gradeCoord sgn ζ x.1 * gradeCoord sgn ζ x.2.1 *
        gradeCoord sgn ζ x.2.2) = fullSum titsCoeff (gradeCoord sgn ζ) := rfl
  rw [hfs, ← Complex.ofReal_pow, Complex.re_ofReal_mul, fullSum_re hD, sum_gradeCoord_cube,
    Finset.sum_congr rfl fun t ht => (titsValue_eq_tV sgn ζ ht).symm]
  have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 6 ≠ 0 := by positivity
  have key : Real.sqrt 6 * (Real.sqrt 6)⁻¹ ^ 3 = 1 / 6 := by
    field_simp; exact hsq.symm
  rw [← mul_assoc, key]
  ring

/-- Non-vacuity of clause (3): every choice of coordinates `ζ_p` is realized by a field `X ∈ J_T`. -/
theorem tits_field_exists (sgn : SignedPlaneIndex → Bool) (ζ : SignedPlaneIndex → ℂ) :
    ∃ X : CompactTits, CompactTits.coordinates X = ((Real.sqrt 6)⁻¹ : ℂ) •
      ∑ p, (ζ p • titsBasis (signedGrade p (sgn p)).val +
        star (ζ p) • titsBasis (-(signedGrade p (sgn p)).val)) := by
  have hfix : compactInvolution (((Real.sqrt 6)⁻¹ : ℂ) •
      ∑ p, (ζ p • titsBasis (signedGrade p (sgn p)).val +
        star (ζ p) • titsBasis (-(signedGrade p (sgn p)).val))) = ((Real.sqrt 6)⁻¹ : ℂ) •
      ∑ p, (ζ p • titsBasis (signedGrade p (sgn p)).val +
        star (ζ p) • titsBasis (-(signedGrade p (sgn p)).val)) := ?_
  · exact ⟨CompactTits.ofFixed _ hfix, rfl⟩
  rw [compactInvolution_complex_smul, map_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_add, compactInvolution_complex_smul, compactInvolution_complex_smul,
      titsBasis_involution, titsBasis_involution, neg_neg, star_star, add_comm]

/-- Graded cubic expansion, every clause. -/
theorem thirteenPlaneCubicFull : Statements.ThirteenPlaneCubicFull := by
  refine ⟨thirteenPlaneCubic, ?_, ?_, ?_, titsThirteenPlaneCubic⟩
  · intro fZ fX fφ hZ hX hφ
    obtain ⟨h1, -, h3⟩ := titsLemma.2.2.2.2.2.2.2.2 fZ fX fφ hZ hX hφ
    exact ⟨h1, h3⟩
  · intro g hg
    refine ⟨?_, ?_⟩
    · rw [titsBasis_product_dependent _ _ ⟨1, -1, Or.inl one_ne_zero, by simp⟩,
        titsBasis_involution, charge_add_self]
    · rw [titsBasis_involution, titsBasis_product_dependent _ _ ⟨1, 1, Or.inl one_ne_zero, by simp⟩,
        add_neg_cancel, titsBasis_zero]
  · intro v w k l hd
    rw [titsBasis_product_independent v w k l hd, tf_smul_left, titsBasis_traceForm,
      if_pos (by abel)]
    ring

end

end ThirteenPlanes.AlbertGrading
