module

public import ThirteenPlanes.Basins.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

set_option backward.privateInPublic true

/-! The relative variance of the field energy on the coupling plane as a rational function.

With `W = a² + 3 lam b²` (`weightedStrength`) and `n` the number of fields,

  `D(a, b) = (2(n-2) W² + 6(n+2) lam b³ (3(1-lam) b - 4a)) / ((n+4)(n+6) W²)`.

`D` is homogeneous of degree zero, and its derivative along any curve `(α, β)` is
`-κ w / W³ · (α β' - β α')`, where `w = b² (a - b)(a + lam b)` is the wedge polynomial of the planar
flow and `κ = 72 (n+2) lam / ((n+4)(n+6))`. -/

open Set

namespace ThirteenPlanes

noncomputable section

/-- Numerator of the relative variance of the field energy on the coupling plane. -/
def anisotropyNum (n lam : ℝ) (u : ℝ × ℝ) : ℝ :=
  2 * (n - 2) * weightedStrength lam u.1 u.2 ^ 2 +
    6 * (n + 2) * lam * (u.2 ^ 3 * (3 * (1 - lam) * u.2 - 4 * u.1))

/-- Denominator of the relative variance of the field energy on the coupling plane. -/
def anisotropyDen (n lam : ℝ) (u : ℝ × ℝ) : ℝ :=
  (n + 4) * (n + 6) * weightedStrength lam u.1 u.2 ^ 2

/-- The relative variance of the field energy of `a D + b C` as a rational function of `(a, b)`. -/
def anisotropyRational (n lam : ℝ) (u : ℝ × ℝ) : ℝ :=
  anisotropyNum n lam u / anisotropyDen n lam u

/-- The wedge polynomial `b² (a - b)(a + lam b)` of the planar one-loop flow. -/
def ratioWedge (lam : ℝ) (u : ℝ × ℝ) : ℝ := u.2 ^ 2 * (u.1 - u.2) * (u.1 + lam * u.2)

/-- The constant `κ = 72 (n+2) lam / ((n+4)(n+6))` in the angular derivative of `D`. -/
def anisotropySlope (n lam : ℝ) : ℝ := 72 * (n + 2) * lam / ((n + 4) * (n + 6))

/-- The angular derivative `-κ w / W³` of `D`. -/
def anisotropyAngular (n lam : ℝ) (u : ℝ × ℝ) : ℝ :=
  -(anisotropySlope n lam) * ratioWedge lam u / weightedStrength lam u.1 u.2 ^ 3

theorem ratioWedge_eq_zero_iff {lam : ℝ} {u : ℝ × ℝ} :
    ratioWedge lam u = 0 ↔ u.2 = 0 ∨ u.1 = u.2 ∨ u.1 = -lam * u.2 := by
  unfold ratioWedge
  simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (by rw [h]; ring)

theorem anisotropySlope_pos {n lam : ℝ} (hn : 0 < n) (hlam : 0 < lam) :
    0 < anisotropySlope n lam := by
  unfold anisotropySlope; positivity

/-- The derivative identity behind the angular derivative (pure algebra). -/
private theorem deriv_identity (n lam a b a' b' : ℝ) (hn4 : n + 4 ≠ 0) (hn6 : n + 6 ≠ 0)
    (hW : a ^ 2 + 3 * lam * b ^ 2 ≠ 0) :
    ((2 * (n - 2) * (2 * (a ^ 2 + 3 * lam * b ^ 2) * (2 * a * a' + 3 * lam * (2 * b * b'))) +
        6 * (n + 2) * lam * (3 * b ^ 2 * b' * (3 * (1 - lam) * b - 4 * a) +
          b ^ 3 * (3 * (1 - lam) * b' - 4 * a'))) *
        ((n + 4) * (n + 6) * (a ^ 2 + 3 * lam * b ^ 2) ^ 2) -
      (2 * (n - 2) * (a ^ 2 + 3 * lam * b ^ 2) ^ 2 +
        6 * (n + 2) * lam * (b ^ 3 * (3 * (1 - lam) * b - 4 * a))) *
        ((n + 4) * (n + 6) * (2 * (a ^ 2 + 3 * lam * b ^ 2) *
          (2 * a * a' + 3 * lam * (2 * b * b'))))) /
      ((n + 4) * (n + 6) * (a ^ 2 + 3 * lam * b ^ 2) ^ 2) ^ 2 =
    -(72 * (n + 2) * lam / ((n + 4) * (n + 6))) * (b ^ 2 * (a - b) * (a + lam * b)) /
        (a ^ 2 + 3 * lam * b ^ 2) ^ 3 * (a * b' - b * a') := by
  field_simp
  ring

/-- Derivative of `D` along a curve, within any set. -/
theorem hasDerivWithinAt_anisotropyRational {n lam : ℝ} (hn4 : n + 4 ≠ 0) (hn6 : n + 6 ≠ 0)
    {α β : ℝ → ℝ} {α' β' s : ℝ} {S : Set ℝ}
    (hα : HasDerivWithinAt α α' S s) (hβ : HasDerivWithinAt β β' S s)
    (hW : weightedStrength lam (α s) (β s) ≠ 0) :
    HasDerivWithinAt (fun r ↦ anisotropyRational n lam (α r, β r))
      (anisotropyAngular n lam (α s, β s) * (α s * β' - β s * α')) S s := by
  have hWd : HasDerivWithinAt (fun r ↦ α r ^ 2 + 3 * lam * β r ^ 2)
      (2 * α s * α' + 3 * lam * (2 * β s * β')) S s := by
    have := (hα.pow 2).add ((hβ.pow 2).const_mul (3 * lam))
    convert this using 1; simp
  have hN : HasDerivWithinAt (fun r ↦ anisotropyNum n lam (α r, β r))
      (2 * (n - 2) * (2 * (α s ^ 2 + 3 * lam * β s ^ 2) *
          (2 * α s * α' + 3 * lam * (2 * β s * β'))) +
        6 * (n + 2) * lam * (3 * β s ^ 2 * β' * (3 * (1 - lam) * β s - 4 * α s) +
          β s ^ 3 * (3 * (1 - lam) * β' - 4 * α'))) S s := by
    have := ((hWd.pow 2).const_mul (2 * (n - 2))).add
      (((hβ.pow 3).mul ((hβ.const_mul (3 * (1 - lam))).sub (hα.const_mul 4))).const_mul
        (6 * (n + 2) * lam))
    convert this using 1
    · funext r; simp [anisotropyNum, weightedStrength]
    · simp
  have hD : HasDerivWithinAt (fun r ↦ anisotropyDen n lam (α r, β r))
      ((n + 4) * (n + 6) * (2 * (α s ^ 2 + 3 * lam * β s ^ 2) *
          (2 * α s * α' + 3 * lam * (2 * β s * β')))) S s := by
    have := (hWd.pow 2).const_mul ((n + 4) * (n + 6))
    convert this using 1
    · funext r; simp [anisotropyDen, weightedStrength]
    · simp
  have hD0 : anisotropyDen n lam (α s, β s) ≠ 0 := by
    unfold anisotropyDen; exact mul_ne_zero (mul_ne_zero hn4 hn6) (pow_ne_zero 2 hW)
  refine (hN.div hD hD0).congr_deriv ?_
  simp only [anisotropyNum, anisotropyDen, anisotropyAngular, anisotropySlope, ratioWedge,
    weightedStrength] at hW ⊢
  exact deriv_identity n lam (α s) (β s) α' β' hn4 hn6 hW

/-- Derivative of `D` along a curve. -/
theorem hasDerivAt_anisotropyRational {n lam : ℝ} (hn4 : n + 4 ≠ 0) (hn6 : n + 6 ≠ 0)
    {α β : ℝ → ℝ} {α' β' s : ℝ} (hα : HasDerivAt α α' s) (hβ : HasDerivAt β β' s)
    (hW : weightedStrength lam (α s) (β s) ≠ 0) :
    HasDerivAt (fun r ↦ anisotropyRational n lam (α r, β r))
      (anisotropyAngular n lam (α s, β s) * (α s * β' - β s * α')) s := by
  rw [← hasDerivWithinAt_univ] at hα hβ ⊢
  exact hasDerivWithinAt_anisotropyRational hn4 hn6 hα hβ hW

theorem anisotropyAngular_eq_zero_iff {n lam : ℝ} (hn : 0 < n) (hlam : 0 < lam) {u : ℝ × ℝ}
    (hu : u ≠ 0) :
    anisotropyAngular n lam u = 0 ↔ u.2 = 0 ∨ u.1 = u.2 ∨ u.1 = -lam * u.2 := by
  have hW := weightedStrength_pos hlam (a := u.1) (b := u.2) (by simpa using hu)
  have hk := anisotropySlope_pos hn hlam
  rw [← ratioWedge_eq_zero_iff, anisotropyAngular, div_eq_zero_iff, neg_mul, neg_eq_zero,
    mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hk.ne'
    · exact h
    · exact absurd h (pow_ne_zero 3 hW.ne')
  · intro h; exact Or.inl (Or.inr h)

/-! The projective line of ratios, parametrized by the unit circle. -/

/-- On the unit circle, the derivative of `θ ↦ D(cos θ, sin θ)` is the angular derivative. -/
theorem hasDerivAt_anisotropyRational_circle {n lam : ℝ} (hn : 0 < n) (hlam : 0 < lam)
    (θ : ℝ) :
    HasDerivAt (fun θ ↦ anisotropyRational n lam (Real.cos θ, Real.sin θ))
      (anisotropyAngular n lam (Real.cos θ, Real.sin θ)) θ := by
  have hu : ((Real.cos θ, Real.sin θ) : ℝ × ℝ) ≠ 0 := by
    intro h
    have h1 : Real.cos θ = 0 := congrArg Prod.fst h
    have h2 : Real.sin θ = 0 := congrArg Prod.snd h
    have := Real.sin_sq_add_cos_sq θ
    rw [h1, h2] at this; norm_num at this
  have hW := weightedStrength_pos hlam (a := Real.cos θ) (b := Real.sin θ) (by simpa using hu)
  have := hasDerivAt_anisotropyRational (n := n) (lam := lam) (by linarith) (by linarith)
    (Real.hasDerivAt_cos θ) (Real.hasDerivAt_sin θ) hW.ne'
  convert this using 1
  have := Real.sin_sq_add_cos_sq θ
  rw [show Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ = 1 by nlinarith, mul_one]

/-- **Critical points on the projective line.** The derivative of `D` along the unit circle
vanishes exactly at the three stationary ratios `b = 0`, `a = b`, `a = -lam b`. -/
theorem anisotropyRational_circle_critical_iff {n lam : ℝ} (hn : 0 < n) (hlam : 0 < lam)
    (θ : ℝ) :
    deriv (fun θ ↦ anisotropyRational n lam (Real.cos θ, Real.sin θ)) θ = 0 ↔
      Real.sin θ = 0 ∨ Real.cos θ = Real.sin θ ∨ Real.cos θ = -lam * Real.sin θ := by
  rw [(hasDerivAt_anisotropyRational_circle hn hlam θ).deriv]
  have hu : ((Real.cos θ, Real.sin θ) : ℝ × ℝ) ≠ 0 := by
    intro h
    have h1 : Real.cos θ = 0 := congrArg Prod.fst h
    have h2 : Real.sin θ = 0 := congrArg Prod.snd h
    have := Real.sin_sq_add_cos_sq θ
    rw [h1, h2] at this; norm_num at this
  exact anisotropyAngular_eq_zero_iff hn hlam hu

end

end ThirteenPlanes
