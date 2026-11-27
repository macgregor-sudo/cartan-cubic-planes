/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Peirce.Clifford

@[expose] public section

set_option backward.privateInPublic true

/-! Contract the normalized round pair identity in the half Peirce space. -/

namespace ThirteenPlanes.Nonharmonic

open scoped BigOperators RealInnerProductSpace
open Peirce

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {h : SymmetricCubic V} {a : V}
  (round : IsRound h 1) (ha : IsUnitIdempotent h a)

local notation "H" => halfSpace h a
local notation "M" => minusSpace h a

/-- The minus component of the product of two half-space vectors. -/
def halfRemainder (x y : H) : M :=
  ⟨h.L x.val y.val - ((1 / 2 : ℝ) * ⟪x, y⟫) • a,
    half_mul_half_sub_line round ha x.property y.property⟩

theorem inner_halfRemainder (x y : H) (u : M) :
    ⟪halfRemainder round ha x y, u⟫ = ⟪halfAction round ha u x, y⟫ := by
  have horth : ⟪a, u.val⟫ = 0 :=
    (spectralSplit round ha).minus_perp.inner_eq (Submodule.mem_span_singleton_self a) u.property
  change ⟪h.L x.val y.val - ((1 / 2 : ℝ) * ⟪x, y⟫) • a, u.val⟫ =
    ⟪h.L u.val x.val, y.val⟫
  rw [inner_sub_left, real_inner_smul_left, horth, mul_zero, sub_zero]
  change h.apply x.val y.val u.val = h.apply u.val x.val y.val
  rw [h.apply_swap₁₂ u.val x.val y.val, h.apply_swap₂₃ x.val u.val y.val]

/-- The pair identity after removing the idempotent component. -/
theorem half_pair (x y : H) :
    ⟪halfRemainder round ha x x, halfRemainder round ha y y⟫ +
      2 * ‖halfRemainder round ha x y‖ ^ 2 =
      (3 / 4 : ℝ) * (‖x‖ ^ 2 * ‖y‖ ^ 2) + (3 / 2 : ℝ) * ⟪x, y⟫ ^ 2 := by
  have horth (u : M) : ⟪a, u.val⟫ = 0 :=
    (spectralSplit round ha).minus_perp.inner_eq (Submodule.mem_span_singleton_self a) u.property
  have hinner (s t : ℝ) (u v : M) :
      ⟪s • a + u.val, t • a + v.val⟫ = s * t + ⟪u, v⟫ := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ha.norm_eq_one, one_pow, horth,
      show ⟪u.val, a⟫ = 0 from (real_inner_comm _ _).trans (horth u),
      mul_zero, mul_one, add_zero, zero_add]
    change t * s + ⟪u, v⟫ = s * t + ⟪u, v⟫
    rw [mul_comm t s]
  have hprod (v w : H) :
      h.L v.val w.val = ((1 / 2 : ℝ) * ⟪v, w⟫) • a + (halfRemainder round ha v w).val := by
    change h.L v.val w.val = _ + (h.L v.val w.val - _)
    abel
  have hp := RoundCubics.pair round x.val y.val
  rw [← real_inner_self_eq_norm_sq (h.L x.val y.val), hprod x x, hprod y y,
    hprod x y, hinner, hinner] at hp
  change (1 / 2 : ℝ) * ⟪x, x⟫ * ((1 / 2 : ℝ) * ⟪y, y⟫) +
    ⟪halfRemainder round ha x x, halfRemainder round ha y y⟫ +
    2 * ((1 / 2 : ℝ) * ⟪x, y⟫ * ((1 / 2 : ℝ) * ⟪x, y⟫) +
      ⟪halfRemainder round ha x y, halfRemainder round ha x y⟫) =
    1 * (‖x‖ ^ 2 * ‖y‖ ^ 2 + 2 * ⟪x, y⟫ ^ 2) at hp
  simp only [real_inner_self_eq_norm_sq, one_mul] at hp
  linear_combination hp

theorem halfAction_isSymmetric (u : M) : (halfAction round ha u).IsSymmetric := by
  intro x y
  exact h.L_isSymmetric u.val x.val y.val

/-- The squared norm of the half action, in the unscaled cubic convention. -/
theorem halfAction_norm_sq (u : M) (x : H) :
    ‖halfAction round ha u x‖ ^ 2 = (3 / 4 : ℝ) * ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
  have hc := congrArg (fun T : Module.End ℝ H => ⟪T x, x⟫) (clifford_relation round ha u u)
  simp only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self, inner_add_left, real_inner_smul_left,
    halfAction_isSymmetric round ha u (halfAction round ha u x) x,
    real_inner_self_eq_norm_sq] at hc
  linarith only [hc]

variable [FiniteDimensional ℝ V]

/-- The trace of the half action is represented by the sum of the diagonal minus components. -/
def halfTraceVector : M :=
  let e := stdOrthonormalBasis ℝ H
  ∑ i, halfRemainder round ha (e i) (e i)

theorem trace_halfAction_eq_inner (u : M) :
    LinearMap.trace ℝ H (halfAction round ha u) = ⟪halfTraceVector round ha, u⟫ := by
  let e := stdOrthonormalBasis ℝ H
  rw [SymmetricCubic.trace_eq_sum_inner e, halfTraceVector]
  change _ = ⟪∑ i, halfRemainder round ha (e i) (e i), u⟫
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_halfRemainder, real_inner_comm (e i)]

private theorem sum_norm_sq_halfRemainder (x : H) :
    let e := stdOrthonormalBasis ℝ H
    ∑ j, ‖halfRemainder round ha x (e j)‖ ^ 2 =
      (3 / 4 : ℝ) * Module.finrank ℝ M * ‖x‖ ^ 2 := by
  let e := stdOrthonormalBasis ℝ H
  let b := stdOrthonormalBasis ℝ M
  change ∑ j, ‖halfRemainder round ha x (e j)‖ ^ 2 = _
  calc
    _ = ∑ j, ∑ i, ⟪halfAction round ha (b i) x, e j⟫ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← b.sum_sq_inner_left (halfRemainder round ha x (e j))]
      simp only [inner_halfRemainder]
    _ = ∑ i, ∑ j, ⟪halfAction round ha (b i) x, e j⟫ ^ 2 := Finset.sum_comm
    _ = ∑ i, ‖halfAction round ha (b i) x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_sq_inner_left _
    _ = _ := by
      simp only [halfAction_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The trace vector acts on the half space by a quadratic form proportional to the norm. -/
theorem halfTraceVector_quadratic (x : H) :
    ⟪halfAction round ha (halfTraceVector round ha) x, x⟫ =
      (3 / 4 : ℝ) * (Module.finrank ℝ H + 2 - 2 * Module.finrank ℝ M) * ‖x‖ ^ 2 := by
  let e := stdOrthonormalBasis ℝ H
  have hp : ∑ i, (⟪halfRemainder round ha x x, halfRemainder round ha (e i) (e i)⟫ +
      2 * ‖halfRemainder round ha x (e i)‖ ^ 2) =
      ∑ i, ((3 / 4 : ℝ) * (‖x‖ ^ 2 * ‖e i‖ ^ 2) + (3 / 2 : ℝ) * ⟪x, e i⟫ ^ 2) :=
    Finset.sum_congr rfl fun i _ => half_pair round ha x (e i)
  simp only [e.orthonormal.norm_eq_one, one_pow, mul_one, Finset.sum_add_distrib,
    ← inner_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hp
  rw [e.sum_sq_inner_left, sum_norm_sq_halfRemainder round ha] at hp
  change ⟪halfRemainder round ha x x, halfTraceVector round ha⟫ +
    2 * ((3 / 4 : ℝ) * Module.finrank ℝ M * ‖x‖ ^ 2) = _ at hp
  rw [inner_halfRemainder] at hp
  linear_combination hp

end

end ThirteenPlanes.Nonharmonic
