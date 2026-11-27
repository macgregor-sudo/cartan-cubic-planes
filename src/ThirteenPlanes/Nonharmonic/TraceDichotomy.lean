/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Nonharmonic.TraceContraction

@[expose] public section

set_option backward.privateInPublic true

/-! The trace dichotomy for normalized round cubics with nonzero half space. -/

namespace ThirteenPlanes.Nonharmonic

open scoped RealInnerProductSpace
open Peirce

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section TraceVector

variable {h : SymmetricCubic V} {a : V}
  (round : IsRound h 1) (ha : IsUnitIdempotent h a)

local notation "H" => halfSpace h a
local notation "M" => minusSpace h a

/-- The operator of the trace vector is scalar, by symmetry and the quadratic contraction. -/
theorem halfTraceVector_action :
    halfAction round ha (halfTraceVector round ha) =
      ((3 / 4 : ℝ) * (Module.finrank ℝ H + 2 - 2 * Module.finrank ℝ M)) •
        (LinearMap.id : Module.End ℝ H) := by
  let c : ℝ := (3 / 4 : ℝ) * (Module.finrank ℝ H + 2 - 2 * Module.finrank ℝ M)
  change halfAction round ha (halfTraceVector round ha) = c • (LinearMap.id : Module.End ℝ H)
  have hs : (c • (LinearMap.id : Module.End ℝ H)).IsSymmetric := by
    intro x y
    simp only [LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left,
      real_inner_smul_right]
  apply sub_eq_zero.mp
  apply ((halfAction_isSymmetric round ha (halfTraceVector round ha)).sub hs).inner_map_self_eq_zero.mp
  intro x
  simp only [LinearMap.sub_apply, inner_sub_left, halfTraceVector_quadratic,
    LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact sub_self _

omit [FiniteDimensional ℝ V] in
private theorem squared_scalar_of_halfAction (u : M) (r : ℝ) (x : H) (hx : x ≠ 0)
    (hscalar : halfAction round ha u x = r • x) :
    r ^ 2 = (3 / 4 : ℝ) * ‖u‖ ^ 2 := by
  have hn := halfAction_norm_sq round ha u x
  rw [hscalar, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hn
  exact mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) hn

end TraceVector

/-- For a nonzero half space, either the idempotent slice and every half action have zero
trace, or the minus space is one-dimensional and its unit direction acts by a scalar
whose square is (3/4). -/
theorem traceDichotomy (h : SymmetricCubic V) (round : IsRound h 1) {a : V}
    (ha : IsUnitIdempotent h a) (hH : Nontrivial (halfSpace h a)) :
    (LinearMap.trace ℝ V (h.L a) = 0 ∧
      ∀ u : minusSpace h a, LinearMap.trace ℝ (halfSpace h a) (halfAction round ha u) = 0) ∨
    ∃ u : minusSpace h a, ‖u‖ = 1 ∧ Module.finrank ℝ (minusSpace h a) = 1 ∧
      ∃ r : ℝ, r ^ 2 = 3 / 4 ∧ ∀ y : halfSpace h a, halfAction round ha u y = r • y := by
  let H := halfSpace h a
  let M := minusSpace h a
  let k : ℝ := Module.finrank ℝ H
  let m : ℝ := Module.finrank ℝ M
  let δ := k + 2 - 2 * m
  let c := (3 / 4 : ℝ) * δ
  let τ := halfTraceVector round ha
  let A := halfAction round ha
  let := hH
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hA : A τ = c • (LinearMap.id : Module.End ℝ H) := halfTraceVector_action round ha
  have hscalar (y : H) : A τ y = c • y := by
    rw [hA, LinearMap.smul_apply, LinearMap.id_apply]
  have hsq : c ^ 2 = (3 / 4 : ℝ) * ‖τ‖ ^ 2 :=
    squared_scalar_of_halfAction round ha τ c x hx (hscalar x)
  have ht₀ := trace_halfAction_eq_inner round ha τ
  change LinearMap.trace ℝ H (A τ) = ⟪τ, τ⟫ at ht₀
  rw [hA, map_smul, smul_eq_mul, LinearMap.trace_id, real_inner_self_eq_norm_sq] at ht₀
  have ht : c * k = ‖τ‖ ^ 2 := ht₀
  have hδprod : δ * (δ - k) = 0 := by
    have hp := hsq
    rw [← ht] at hp
    dsimp only [c] at hp
    nlinarith only [hp]
  rcases mul_eq_zero.mp hδprod with hδ | hδ
  · left
    have hc : c = 0 := by dsimp [c]; rw [hδ, mul_zero]
    have hτsq : ‖τ‖ ^ 2 = 0 := by
      rw [hc] at hsq
      linarith only [hsq]
    have hτ : τ = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hτsq)
    refine ⟨?_, ?_⟩
    · rw [trace_formula round ha]
      change 1 - m + (1 / 2 : ℝ) * k = 0
      change k + 2 - 2 * m = 0 at hδ
      linarith only [hδ]
    · intro u
      rw [trace_halfAction_eq_inner round ha]
      change ⟪τ, u⟫ = 0
      rw [hτ, inner_zero_left]
  · right
    have hMk : m = 1 := by
      change k + 2 - 2 * m - k = 0 at hδ
      linarith only [hδ]
    have hM : Module.finrank ℝ M = 1 := by
      change (Module.finrank ℝ M : ℝ) = 1 at hMk
      exact_mod_cast hMk
    have hk : 0 < k := by
      change (0 : ℝ) < Module.finrank ℝ H
      exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℝ H)
    have hc : c ≠ 0 := by
      dsimp only [c]
      rw [sub_eq_zero.mp hδ]
      exact mul_ne_zero (by norm_num) hk.ne'
    have hτ : τ ≠ 0 := by
      intro he
      rw [he, norm_zero, zero_pow two_ne_zero] at ht
      exact mul_ne_zero hc hk.ne' ht
    have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.mpr hτ
    let u := ‖τ‖⁻¹ • τ
    have hu : ‖u‖ = 1 := by
      rw [show u = ‖τ‖⁻¹ • τ from rfl, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg τ)), inv_mul_cancel₀ hn]
    let r := ‖τ‖⁻¹ * c
    have huScalar (y : H) : A u y = r • y := by
      rw [show u = ‖τ‖⁻¹ • τ from rfl, map_smul, LinearMap.smul_apply, hscalar, smul_smul]
    refine ⟨u, hu, hM, r, ?_, huScalar⟩
    have hr := squared_scalar_of_halfAction round ha u r x hx (huScalar x)
    rwa [hu, one_pow, mul_one] at hr

end

end ThirteenPlanes.Nonharmonic
