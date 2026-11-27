module

public import ThirteenPlanes.PeirceDecomposition
public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

/-! Maxima of the cubic on the unit sphere give actual unit idempotents. -/

open scoped RealInnerProductSpace
open Metric

namespace ThirteenPlanes.Peirce

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem cubic_hasStrictFDerivAt (h : SymmetricCubic V) (x : V) :
    HasStrictFDerivAt (fun y => h.apply y y y) ((3 : ℝ) • innerSL ℝ (h.L x x)) x := by
  let B : V →L[ℝ] V →L[ℝ] V := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp h.L)
  have hid : HasStrictFDerivAt (fun y : V => y) (ContinuousLinearMap.id ℝ V) x :=
    hasStrictFDerivAt_id x
  have hB := (B.hasStrictFDerivAt.clm_apply hid).inner ℝ hid
  convert hB using 1
  · rfl
  · ext y
    simp only [smul_apply, innerSL_apply_apply, ContinuousLinearMap.comp_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, smul_eq_mul, inner_add_left]
    change 3 * h.apply x x y = h.apply x x y + (h.apply x y x + h.apply y x x)
    rw [h.apply_swap₁₂ y x x, h.apply_swap₂₃ x y x]
    ring


/-- Every unit-sphere maximum of a normalized round cubic is a unit idempotent. -/
theorem unitIdempotent_of_isMaxOn (h : SymmetricCubic V) (round : IsRound h 1) (x : V)
    (hx : x ∈ sphere (0 : V) 1) (hmax : IsMaxOn (fun y => h.apply y y y) (sphere (0 : V) 1) x) :
    IsUnitIdempotent h x := by
  have hn : ‖x‖ = 1 := by simpa using hx
  let := FiniteDimensional.completeSpace ℝ V
  have hex : IsLocalExtrOn (fun y => h.apply y y y) {y : V | ‖y‖ ^ 2 = ‖x‖ ^ 2} x := by
    have hs : {y : V | ‖y‖ ^ 2 = ‖x‖ ^ 2} = sphere (0 : V) 1 := by
      ext y
      rw [Set.mem_ofPred_eq, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hn]
      simp
    rw [hs]
    exact Or.inr hmax.isLocalMaxOn
  obtain ⟨a, b, hab, hmul⟩ := hex.exists_multipliers_of_hasStrictFDerivAt_1d
    (hasStrictFDerivAt_norm_sq x) (cubic_hasStrictFDerivAt h x)
  have hlinear (y : V) : (2 * a) * ⟪x, y⟫ + (3 * b) * ⟪h.L x x, y⟫ = 0 := by
    have hy := congrFun (congrArg DFunLike.coe hmul) y
    simp only [add_apply, smul_apply,
      zero_apply, innerSL_apply_apply, smul_eq_mul] at hy
    linear_combination hy
  have hb : b ≠ 0 := by
    intro hzero
    have ha := hlinear x
    rw [hzero, real_inner_self_eq_norm_sq, hn] at ha
    have ha0 : a = 0 := by linarith only [ha]
    exact hab (by simp [ha0, hzero])
  let t : ℝ := -(2 * a) / (3 * b)
  have hscale : h.L x x = t • x := by
    apply ext_inner_right ℝ
    intro y
    rw [real_inner_smul_left]
    dsimp only [t]
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (by norm_num) hb)]
    linear_combination hlinear y
  have hL : ‖h.L x x‖ ^ 2 = 1 := by
    simpa [SymmetricCubic.squareMap, hn] using round.square_norm x
  have ht : t ^ 2 = 1 := by
    rw [hscale, norm_smul, hn, mul_one, Real.norm_eq_abs, sq_abs] at hL
    exact hL
  have hneg : -x ∈ sphere (0 : V) 1 := by simp [hn]
  have hnonneg := hmax hneg
  have hc : h.apply x x x = t := by
    change ⟪h.L x x, x⟫ = t
    rw [hscale, real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
    ring
  have hodd : h.apply (-x) (-x) (-x) = -h.apply x x x := by
    change ⟪h.L (-x) (-x), -x⟫ = -⟪h.L x x, x⟫
    simp
  change h.apply (-x) (-x) (-x) ≤ h.apply x x x at hnonneg
  rw [hodd, hc] at hnonneg
  have ht₁ : t = 1 := (sq_eq_sq₀ (by linarith only [hnonneg]) zero_le_one).mp (by simpa using ht)
  exact ⟨hn, by simpa [ht₁] using hscale⟩

/-- In a nonzero finite-dimensional round space, some point attains the unit-sphere maximum. -/
theorem exists_unitIdempotent [Nontrivial V] (h : SymmetricCubic V) (round : IsRound h 1) :
    ∃ x : V, IsUnitIdempotent h x := by
  obtain ⟨u, hu⟩ := exists_norm_eq V (by norm_num : (0 : ℝ) ≤ 1)
  have hne : (sphere (0 : V) 1).Nonempty := ⟨u, by simpa using hu⟩
  have hc : Continuous (fun y => h.apply y y y) :=
    continuous_iff_continuousAt.mpr fun x => (cubic_hasStrictFDerivAt h x).continuousAt
  obtain ⟨x, hx, hm⟩ := (isCompact_sphere (0 : V) 1).exists_isMaxOn hne hc.continuousOn
  exact ⟨x, unitIdempotent_of_isMaxOn h round x hx hm⟩

end

end ThirteenPlanes.Peirce
