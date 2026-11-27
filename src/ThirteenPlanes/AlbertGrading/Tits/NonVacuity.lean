module

public import ThirteenPlanes.AlbertGrading.Tits.ExteriorMain

@[expose] public section

set_option backward.privateInPublic true

/-!
# Non-vacuity of the exterior frame normal form

The frame `(1, ω^a, ω^{-a})/3` is proved directly (without exterior frame normal form) to be a frame of
`J_T` whose plane is orthogonal to `Q₀⁰`, so the hypotheses of `Targets.ExteriorFrame` are
satisfiable. Triples of scalar matrices multiply like the group algebra of `ℤ/3`.
-/

open scoped Matrix RealInnerProductSpace BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem firstTitsJordanProduct_scalar (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℂ) :
    firstTitsJordanProduct (α₁ • (1 : Mat3 ℂ), β₁ • (1 : Mat3 ℂ), γ₁ • (1 : Mat3 ℂ))
      (α₂ • (1 : Mat3 ℂ), β₂ • (1 : Mat3 ℂ), γ₂ • (1 : Mat3 ℂ)) =
      ((α₁ * α₂ + β₁ * γ₂ + β₂ * γ₁) • (1 : Mat3 ℂ), (γ₁ * γ₂ + α₁ * β₂ + α₂ * β₁) • (1 : Mat3 ℂ),
        (β₁ * β₂ + α₁ * γ₂ + α₂ * γ₁) • (1 : Mat3 ℂ)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [firstTitsJordanProduct, sharpPair, trace3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply] <;> ring

private theorem cp_pair_sum (d : ZMod 3) :
    1 + chargePhase d + chargePhase (-d) = if d = 0 then 3 else 0 := by
  have hq := chargeRoot_quadratic
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) d with rfl | rfl | rfl
  · simp; norm_num
  · rw [if_neg (by decide), show chargePhase 1 = chargeRoot from pow_one _,
      show chargePhase (-1) = chargeRoot ^ 2 from rfl]
    linear_combination hq
  · rw [if_neg (by decide), show chargePhase 2 = chargeRoot ^ 2 from rfl,
      show chargePhase (-2) = chargeRoot from pow_one _]
    linear_combination hq

private theorem cp_triple_sum (a b : ZMod 3) :
    chargePhase (-a - b) + chargePhase a + chargePhase b =
      if a = b then 3 * chargePhase a else 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have key : chargePhase (-a - b) + chargePhase a + chargePhase b =
      chargePhase a * (1 + chargePhase (b - a) + chargePhase (-(b - a))) := by
    rw [mul_add, mul_add, mul_one, ← chargePhase_add, ← chargePhase_add]
    have e1 : -a - b = a + -(b - a) := by linear_combination (-a) * h3
    have e2 : b = a + (b - a) := by ring
    rw [e1]
    nth_rewrite 3 [e2]
    ring
  rw [key, cp_pair_sum]
  by_cases hab : a = b
  · subst hab; simp; ring
  · have : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    simp [hab, this]

theorem exteriorPoint_isFrame : IsTitsFrame exteriorPoint := by
  refine ⟨fun a b => ?_, exteriorPoint_trace, ?_⟩
  · have h0 : (1 / 3 : ℂ) * (1 / 3) + 1 / 3 * chargePhase a * (1 / 3 * chargePhase (-b)) +
        1 / 3 * chargePhase b * (1 / 3 * chargePhase (-a)) = if a = b then 1 / 3 else 0 := by
      have e : chargePhase a * chargePhase (-b) = chargePhase (a - b) := by
        rw [← chargePhase_add, sub_eq_add_neg]
      have e' : chargePhase b * chargePhase (-a) = chargePhase (-(a - b)) := by
        rw [← chargePhase_add, neg_sub, sub_eq_add_neg]
      calc _ = (1 / 9) * (1 + chargePhase a * chargePhase (-b) + chargePhase b * chargePhase (-a)) := by
              ring
        _ = (1 / 9) * (1 + chargePhase (a - b) + chargePhase (-(a - b))) := by rw [e, e']
        _ = _ := by
          rw [cp_pair_sum]
          by_cases hab : a = b
          · simp [hab]; norm_num
          · simp [hab, sub_eq_zero]
    have h1 : 1 / 3 * chargePhase (-a) * (1 / 3 * chargePhase (-b)) + 1 / 3 * (1 / 3 * chargePhase b) +
        1 / 3 * (1 / 3 * chargePhase a) = if a = b then 1 / 3 * chargePhase a else 0 := by
      have e : chargePhase (-a) * chargePhase (-b) = chargePhase (-a - b) := by
        rw [← chargePhase_add, sub_eq_add_neg]
      calc _ = (1 / 9) * (chargePhase (-a) * chargePhase (-b) + chargePhase a + chargePhase b) := by
              ring
        _ = _ := by
          rw [e, cp_triple_sum]
          by_cases hab : a = b
          · simp [hab]; ring
          · simp [hab]
    have h2 : 1 / 3 * chargePhase a * (1 / 3 * chargePhase b) + 1 / 3 * (1 / 3 * chargePhase (-b)) +
        1 / 3 * (1 / 3 * chargePhase (-a)) = if a = b then 1 / 3 * chargePhase (-a) else 0 := by
      have e : chargePhase a * chargePhase b = chargePhase (-(-a) - -b) := by
        rw [← chargePhase_add]; congr 1; ring
      calc _ = (1 / 9) * (chargePhase a * chargePhase b + chargePhase (-a) + chargePhase (-b)) := by
              ring
        _ = _ := by
          rw [e, cp_triple_sum]
          by_cases hab : a = b
          · simp [hab]; ring
          · simp [hab]
    apply CompactTits.ext
    rw [coordinates_product, exteriorPoint_coordinates, exteriorPoint_coordinates,
      firstTitsJordanProduct_scalar, h0, h1, h2]
    by_cases hab : a = b
    · subst hab; simp [exteriorPoint_coordinates]
    · simp [hab]
  · have hq := chargeRoot_quadratic
    apply CompactTits.ext
    simp only [map_sum, sum_zmod3, map_add, exteriorPoint_coordinates, neg_zero, chargePhase_zero,
      show chargePhase 1 = chargeRoot from pow_one _, show chargePhase 2 = chargeRoot ^ 2 from rfl,
      show chargePhase (-1) = chargeRoot ^ 2 from rfl, show chargePhase (-2) = chargeRoot from pow_one _,
      Prod.mk_add_mk, CompactTits.coordinates_one, firstTitsOne]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Matrix.zero_apply] <;> split_ifs <;> simp only [mul_one, mul_zero, add_zero]
    · norm_num
    · linear_combination (1 / 3 : ℂ) * hq
    · linear_combination (1 / 3 : ℂ) * hq

theorem exteriorPoint_plane_orthogonal :
    (titsFramePlane exteriorPoint).IsOrtho visibleTraceless := by
  rw [Submodule.isOrtho_iff_le, titsFramePlane, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal]
  rintro u ⟨hu, -⟩
  have hw : (CompactTits.coordinates (exteriorPoint a - (1 / 3 : ℝ) • CompactTits.one)).1 = 0 := by
    rw [map_sub, map_smul, exteriorPoint_coordinates, CompactTits.coordinates_one]
    ext i j
    simp [firstTitsOne, Matrix.one_apply, Complex.real_smul]
  rw [CompactTits.inner_eq_tracePairing, CompactTits.tracePairing, hw, hu]
  simp

/-- The hypotheses of the exterior frame normal form are satisfiable. -/
theorem exteriorFrame_hypotheses_satisfiable :
    ∃ p : ZMod 3 → CompactTits, IsTitsFrame p ∧ (titsFramePlane p).IsOrtho visibleTraceless :=
  ⟨exteriorPoint, exteriorPoint_isFrame, exteriorPoint_plane_orthogonal⟩

end

end ThirteenPlanes.AlbertGrading
