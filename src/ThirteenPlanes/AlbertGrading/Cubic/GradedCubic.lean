module

public import ThirteenPlanes.AlbertGrading.Cubic.Coordinates

@[expose] public section

/-! The normalized cubic of a ternary graded Albert algebra.

For independent grades the coefficient lies in `-(3/2)μ₃`. Expansion on zero-sum grade triples
gives the diagonal cubic terms and one mixed term for each collinear triple. -/

namespace ThirteenPlanes.AlbertGrading

open Grading Grading.JC Cubic

noncomputable section

namespace Cubic

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ) {sgn : SignedPlaneIndex → Bool}
  {u : SignedPlaneIndex → JC}
  (hu : ∀ p, u p ∈ charSpace ρ (signedGrade p (sgn p)).val ∧ IsNormalized (u p))

include hu in
/-- `u_g ∈ A_g` and `u_g` is normalized, for every nonzero grade `g`. -/
theorem gradeUnit_spec (k : NonzeroCharge) :
    gradeUnit sgn u k ∈ charSpace ρ k.val ∧ IsNormalized (gradeUnit sgn u k) := by
  rw [← grade_point_sign k, gradeUnit_signedGrade]
  obtain ⟨hm, hn⟩ := hu (pointOfNZ k)
  by_cases hs : sgnOf k = sgn (pointOfNZ k)
  · rw [ite_eq_left hs, hs]; exact ⟨hm, hn⟩
  · rw [ite_eq_right hs]
    have he : signedGrade (pointOfNZ k) (sgnOf k) =
        oppositeCharge (signedGrade (pointOfNZ k) (sgn (pointOfNZ k))) := by
      rw [← signedGrade_not]; congr 1; cases h1 : sgnOf k <;> cases h2 : sgn (pointOfNZ k) <;> simp_all
    rw [he, opp_val]
    exact ⟨conj_mem_charSpace hm, conj_normalized hn⟩

/-- The coefficients `d(u_a,u_b,u_c) = ⟨u_a ∘ u_b, u_c⟩`. -/
def gradedCoeff (sgn : SignedPlaneIndex → Bool) (u : SignedPlaneIndex → JC) : Coeff :=
  fun a b c => ip (mul (gradeUnit sgn u a) (gradeUnit sgn u b)) (gradeUnit sgn u c)

include hρ hu in
theorem gradedCoeff_data (ζ : SignedPlaneIndex → ℂ) :
    CubicData (gradedCoeff sgn u) (gradeCoord sgn ζ) where
  zero a b c h := cubic_grade hρ (gradeUnit_spec hu a).1 (gradeUnit_spec hu b).1
    (gradeUnit_spec hu c).1 h
  swap12 a b c := by unfold gradedCoeff; rw [JC.mul_comm]
  swap23 a b c := D_swap23 _ _ _
  neg a b c := by
    unfold gradedCoeff
    rw [gradeUnit_opp, gradeUnit_opp, gradeUnit_opp, ← conj_mul, ip_conj]
  diag k := by
    unfold gradedCoeff
    have hn := (gradeUnit_spec hu k).2
    rw [hn.1, ip_comm, ip_conj_normalized hn]
  coord k := gradeCoord_opp sgn ζ k

/-! ## Multilinear expansion in `J_ℂ` -/

/-- The product as a bilinear map. -/
def mulBil : JC →ₗ[ℂ] JC →ₗ[ℂ] JC :=
  LinearMap.mk₂ ℂ mul mul_add_left mul_smul_left mul_add_right mul_smul_right

/-- The form as a bilinear map. -/
def ipBil : JC →ₗ[ℂ] JC →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ ip ip_add_left ip_smul_left ip_add_right ip_smul_right

theorem ip_mul_sum (c : ℂ) (Z : NonzeroCharge → ℂ) (U : NonzeroCharge → JC) :
    ip (mul (c • ∑ k, Z k • U k) (c • ∑ k, Z k • U k)) (c • ∑ k, Z k • U k) =
      c ^ 3 * ∑ x : Triple, ip (mul (U x.1) (U x.2.1)) (U x.2.2) * Z x.1 * Z x.2.1 * Z x.2.2 := by
  have e1 : ∀ x y, mul x y = mulBil x y := fun _ _ => rfl
  have e2 : ∀ x y, ip x y = ipBil x y := fun _ _ => rfl
  simp only [e1, e2, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

end Cubic

open Cubic in
/-- Graded cubic expansion (display thirteen-field polynomial), for every ternary grading group. -/
theorem thirteenPlaneCubic : Statements.ThirteenPlaneCubic := by
  intro ρ hρ sgn u hu
  refine ⟨?_, ?_⟩
  · -- clause (a): the phases
    intro t ht x hx
    have hxr := mem_repsF.mpr hx
    obtain ⟨p1, p2, -⟩ := proper_of_mem_reps ht hxr
    have hs : x.1.val + x.2.1.val + x.2.2.val = 0 := (mem_repsF.mpr hx |> fun h => by
      rw [repsF, Finset.mem_filter] at h; exact h.2.1)
    have hc : x.2.2.val = -(x.1.val + x.2.1.val) := by linear_combination hs
    have h₁ : x.1.val + x.2.1.val ≠ 0 := by
      intro h; apply x.2.2.property; rw [hc, h, neg_zero]
    have h₂ : x.1.val - x.2.1.val ≠ 0 := by
      intro h; apply p1; rw [Subtype.ext (sub_eq_zero.mp h)]
    have m3 := (gradeUnit_spec hu x.2.2).1
    rw [hc] at m3
    exact phase_mu3 hρ x.1.property x.2.1.property h₁ h₂ (gradeUnit_spec hu x.1).1
      (gradeUnit_spec hu x.1).2 (gradeUnit_spec hu x.2.1).1 (gradeUnit_spec hu x.2.1).2 m3
      (gradeUnit_spec hu x.2.2).2
  · intro ζ X hX
    have hD := gradedCoeff_data hρ hu ζ
    refine ⟨fun t ht x hx => tT_eq_tV hD ht hx, ?_⟩
    have hXs : of (X : Glennie.Albert) = (((Real.sqrt 6)⁻¹ : ℝ) : ℂ) •
        ∑ k, gradeCoord sgn ζ k • gradeUnit sgn u k := by
      rw [hX, sum_field]; push_cast; rfl
    rw [apply_eq_ip', hXs, ip_mul_sum]
    have hfs : (∑ x : Triple, ip (mul (gradeUnit sgn u x.1) (gradeUnit sgn u x.2.1))
        (gradeUnit sgn u x.2.2) * gradeCoord sgn ζ x.1 * gradeCoord sgn ζ x.2.1 *
          gradeCoord sgn ζ x.2.2) = fullSum (gradedCoeff sgn u) (gradeCoord sgn ζ) := rfl
    rw [hfs, ← Complex.ofReal_pow, Complex.re_ofReal_mul, fullSum_re hD, sum_gradeCoord_cube]
    change Real.sqrt 6 * ((Real.sqrt 6)⁻¹ ^ 3 * (3 * (2 * ∑ p, (ζ p ^ 3).re) -
        18 * ∑ t ∈ signedCollinearTriples, tV (gradedCoeff sgn u) (gradeCoord sgn ζ) t)) =
      ∑ p, (ζ p ^ 3).re - 3 * ∑ t ∈ signedCollinearTriples,
        tV (gradedCoeff sgn u) (gradeCoord sgn ζ) t
    have h0 : Real.sqrt 6 ≠ 0 := by positivity
    have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have key : Real.sqrt 6 * (Real.sqrt 6)⁻¹ ^ 3 = 1 / 6 := by
      field_simp; exact hsq.symm
    rw [← mul_assoc, key]
    ring

end

end ThirteenPlanes.AlbertGrading
