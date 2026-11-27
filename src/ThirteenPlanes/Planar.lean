module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

/-! The scalar one-loop vector field in homogeneous couplings. -/

namespace ThirteenPlanes

noncomputable section

/-- The physical beta-function denominator. -/
def flowScale : ℝ := 16 * Real.pi ^ 2

theorem flowScale_pos : 0 < flowScale := by
  unfold flowScale
  positivity [Real.pi_pos]

theorem flowScale_ne_zero : flowScale ≠ 0 := ne_of_gt flowScale_pos

/-- The coefficient of the identity in the double contraction. -/
def familyM (lam : ℝ) (u : ℝ × ℝ) : ℝ := u.1 ^ 2 / 3 + lam * u.2 ^ 2

/-- The coefficient of the diagonal cubic in the triangle contraction. -/
def familyP (lam : ℝ) (u : ℝ × ℝ) : ℝ := -lam * u.2 ^ 3 / 2

/-- The coefficient of the mixing cubic in the triangle contraction. -/
def familyQ (lam : ℝ) (u : ℝ × ℝ) : ℝ := ((1 - lam) * u.2 ^ 3 - u.1 * u.2 ^ 2) / 2

/-- The beta function in physical time `ℓ = log (μ₀ / μ)`, for homogeneous couplings. -/
def familyField (lam ε : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (((8 * Real.pi ^ 2 * ε - 3 * familyM lam u / 2) * u.1 - 2 * familyP lam u) / flowScale,
   ((8 * Real.pi ^ 2 * ε - 3 * familyM lam u / 2) * u.2 - 2 * familyQ lam u) / flowScale)

theorem familyField_contDiff (lam ε : ℝ) : ContDiff ℝ ⊤ (familyField lam ε) := by
  unfold familyField familyM familyP familyQ
  apply ContDiff.prodMk <;> simp only [div_eq_mul_inv] <;> fun_prop

theorem familyField_locallyLipschitz (lam ε : ℝ) : LocallyLipschitz (familyField lam ε) :=
  ((familyField_contDiff lam ε).of_le (by simp)).locallyLipschitz

theorem flowScale_mul_familyField_fst (lam ε a b : ℝ) :
    flowScale * (familyField lam ε (a, b)).1 =
      (8 * Real.pi ^ 2 * ε - 3 * familyM lam (a, b) / 2) * a - 2 * familyP lam (a, b) := by
  simp [familyField, flowScale_ne_zero, mul_comm flowScale]

theorem flowScale_mul_familyField_snd (lam ε a b : ℝ) :
    flowScale * (familyField lam ε (a, b)).2 =
      (8 * Real.pi ^ 2 * ε - 3 * familyM lam (a, b) / 2) * b - 2 * familyQ lam (a, b) := by
  simp [familyField, flowScale_ne_zero, mul_comm flowScale]

@[simp] theorem familyField_zero (lam ε : ℝ) : familyField lam ε 0 = 0 := by
  simp [familyField, familyM, familyP, familyQ]

theorem familyField_wedge (lam ε a b : ℝ) :
    flowScale * (a * (familyField lam ε (a, b)).2 - b * (familyField lam ε (a, b)).1) =
      b ^ 2 * (a - b) * (a + lam * b) := by
  rw [mul_sub, mul_left_comm flowScale a, mul_left_comm flowScale b,
    flowScale_mul_familyField_fst, flowScale_mul_familyField_snd]
  simp only [familyM, familyP, familyQ]
  ring

theorem familyField_pureMixing (lam ε b : ℝ) :
    flowScale * (familyField lam ε (0, b)).1 = lam * b ^ 3 := by
  rw [flowScale_mul_familyField_fst]
  simp only [mul_zero, zero_sub, familyP]
  ring

/-- The mixing coordinate has a multiplicative rate, also on its zero line. -/
theorem familyField_mixing_factor (lam ε a b : ℝ) :
    (familyField lam ε (a, b)).2 = b *
      ((8 * Real.pi ^ 2 * ε - 3 * familyM lam (a, b) / 2 + a * b - (1 - lam) * b ^ 2) /
        flowScale) := by
  simp only [familyField, familyQ]
  ring

/-- The signed gap of a nonzero stationary ray has a multiplicative rate. -/
theorem familyField_ray_gap_factor {lam r : ℝ} (hr : (1 - lam + r * lam) * r = 1)
    (ε a b : ℝ) :
    (familyField lam ε (a, b)).2 - r * (familyField lam ε (a, b)).1 = (b - r * a) *
      ((8 * Real.pi ^ 2 * ε - 3 * familyM lam (a, b) / 2 - (1 - lam + r * lam) * b ^ 2) /
        flowScale) := by
  simp only [familyField, familyP, familyQ]
  linear_combination -a * b ^ 2 / flowScale * hr

/-- Shape polynomial in the chart `t = b / a`. -/
def ratioPolynomial (lam t : ℝ) : ℝ := t ^ 2 * (1 - t) * (1 + lam * t)

/-- Strength coefficient in the chart `a = g`, `b = g * t`. -/
def strengthPolynomial (lam t : ℝ) : ℝ := 3 * familyM lam (1, t) + 4 * familyP lam (1, t)

theorem strengthPolynomial_eq (lam t : ℝ) :
    strengthPolynomial lam t = 1 + lam * t ^ 2 * (3 - 2 * t) := by
  simp only [strengthPolynomial, familyM, familyP]
  ring

theorem familyField_strength (lam ε a t : ℝ) :
    flowScale * (familyField lam ε (a, a * t)).1 =
      (flowScale * ε * a - strengthPolynomial lam t * a ^ 3) / 2 := by
  rw [flowScale_mul_familyField_fst, strengthPolynomial_eq]
  simp only [familyM, familyP, flowScale]
  ring

theorem familyField_ratio (lam ε a t : ℝ) :
    flowScale * ((familyField lam ε (a, a * t)).2 - t * (familyField lam ε (a, a * t)).1) =
      a ^ 3 * ratioPolynomial lam t := by
  rw [mul_sub, mul_left_comm flowScale t, flowScale_mul_familyField_fst,
    flowScale_mul_familyField_snd]
  simp only [familyM, familyP, familyQ, ratioPolynomial]
  ring

theorem familyField_ratio_quotient (lam ε a b : ℝ) (ha : a ≠ 0) :
    ((familyField lam ε (a, b)).2 * a - b * (familyField lam ε (a, b)).1) / a ^ 2 =
      a ^ 2 * ratioPolynomial lam (b / a) / flowScale := by
  symm
  apply (div_eq_div_iff flowScale_ne_zero (pow_ne_zero 2 ha)).mpr
  calc
    a ^ 2 * ratioPolynomial lam (b / a) * a ^ 2 = b ^ 2 * (a - b) * (a + lam * b) := by
      rw [ratioPolynomial]
      field_simp
    _ = _ := by rw [← familyField_wedge lam ε a b, mul_comm a, mul_comm flowScale]

theorem familyField_inverseRatio_quotient (lam ε a b : ℝ) (hb : b ≠ 0) :
    ((familyField lam ε (a, b)).1 * b - a * (familyField lam ε (a, b)).2) / b ^ 2 =
      b ^ 2 * (1 - a / b) * (a / b + lam) / flowScale := by
  symm
  apply (div_eq_div_iff flowScale_ne_zero (pow_ne_zero 2 hb)).mpr
  calc
    b ^ 2 * (1 - a / b) * (a / b + lam) * b ^ 2 =
        -(b ^ 2 * (a - b) * (a + lam * b)) := by
      field_simp
      ring
    _ = _ := by
      have hw := familyField_wedge lam ε a b
      linear_combination hw

theorem familyField_hasDerivAt_ratio {lam ε : ℝ} {a b : ℝ → ℝ} {s : ℝ}
    (ha₀ : a s ≠ 0)
    (ha : HasDerivAt a (familyField lam ε (a s, b s)).1 s)
    (hb : HasDerivAt b (familyField lam ε (a s, b s)).2 s) :
    HasDerivAt (fun x ↦ b x / a x)
      ((a s) ^ 2 * ratioPolynomial lam (b s / a s) / flowScale) s := by
  rw [← familyField_ratio_quotient lam ε (a s) (b s) ha₀]
  exact hb.div ha ha₀

theorem familyField_hasDerivWithinAt_ratio {lam ε : ℝ} {a b : ℝ → ℝ} {s : ℝ} {S : Set ℝ}
    (ha₀ : a s ≠ 0)
    (ha : HasDerivWithinAt a (familyField lam ε (a s, b s)).1 S s)
    (hb : HasDerivWithinAt b (familyField lam ε (a s, b s)).2 S s) :
    HasDerivWithinAt (fun x ↦ b x / a x)
      ((a s) ^ 2 * ratioPolynomial lam (b s / a s) / flowScale) S s := by
  rw [← familyField_ratio_quotient lam ε (a s) (b s) ha₀]
  exact hb.div ha ha₀

theorem familyField_hasDerivAt_inverseRatio {lam ε : ℝ} {a b : ℝ → ℝ} {s : ℝ}
    (hb₀ : b s ≠ 0)
    (ha : HasDerivAt a (familyField lam ε (a s, b s)).1 s)
    (hb : HasDerivAt b (familyField lam ε (a s, b s)).2 s) :
    HasDerivAt (fun x ↦ a x / b x)
      ((b s) ^ 2 * (1 - a s / b s) * (a s / b s + lam) / flowScale) s := by
  rw [← familyField_inverseRatio_quotient lam ε (a s) (b s) hb₀]
  exact ha.div hb hb₀

theorem familyField_hasDerivWithinAt_inverseRatio {lam ε : ℝ} {a b : ℝ → ℝ} {s : ℝ}
    {S : Set ℝ} (hb₀ : b s ≠ 0)
    (ha : HasDerivWithinAt a (familyField lam ε (a s, b s)).1 S s)
    (hb : HasDerivWithinAt b (familyField lam ε (a s, b s)).2 S s) :
    HasDerivWithinAt (fun x ↦ a x / b x)
      ((b s) ^ 2 * (1 - a s / b s) * (a s / b s + lam) / flowScale) S s := by
  rw [← familyField_inverseRatio_quotient lam ε (a s) (b s) hb₀]
  exact ha.div hb hb₀

@[simp] theorem familyField_neg (lam ε : ℝ) (u : ℝ × ℝ) :
    familyField lam ε (-u) = -familyField lam ε u := by
  rcases u with ⟨a, b⟩
  ext <;> simp only [familyField, familyM, familyP, familyQ, Prod.fst_neg, Prod.snd_neg] <;> ring

theorem ratioPolynomial_eq_zero_iff {lam t : ℝ} (hlam : lam ≠ 0) :
    ratioPolynomial lam t = 0 ↔ t = 0 ∨ t = 1 ∨ t = -1 / lam := by
  have hroot : 1 + lam * t = 0 ↔ t = -1 / lam := by
    rw [eq_div_iff hlam, mul_comm t lam]
    constructor <;> intro h <;> linarith
  rw [ratioPolynomial, mul_eq_zero, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    or_assoc, sub_eq_zero, hroot, eq_comm (a := (1 : ℝ))]

/-- Full stationarity in the finite ratio chart, with the physical scale retained. -/
theorem familyField_eq_zero_iff_of_mul {lam ε a t : ℝ} (ha : a ≠ 0) :
    familyField lam ε (a, a * t) = 0 ↔
      ratioPolynomial lam t = 0 ∧ a ^ 2 / flowScale * strengthPolynomial lam t = ε := by
  have hs := familyField_strength lam ε a t
  have ht := familyField_ratio lam ε a t
  constructor
  · intro h
    rw [h] at hs ht
    change flowScale * 0 = _ at hs
    change flowScale * (0 - t * 0) = _ at ht
    simp only [mul_zero, sub_zero, zero_eq_mul, pow_eq_zero_iff (by decide : 3 ≠ 0),
      ha, false_or] at ht
    refine ⟨ht, ?_⟩
    have hmul : a * (flowScale * ε - a ^ 2 * strengthPolynomial lam t) = 0 := by
      linear_combination -2 * hs
    have he := (mul_eq_zero.mp hmul).resolve_left ha
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff flowScale_ne_zero).mpr
    linear_combination -he
  · rintro ⟨ht₀, hs₀⟩
    have hrearrange : a ^ 2 * strengthPolynomial lam t = flowScale * ε := by
      calc
        a ^ 2 * strengthPolynomial lam t =
            (a ^ 2 / flowScale * strengthPolynomial lam t) * flowScale := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ flowScale_ne_zero]
        _ = flowScale * ε := by rw [hs₀, mul_comm]
    have hfst : (familyField lam ε (a, a * t)).1 = 0 :=
      (mul_eq_zero.mp (by linear_combination hs - a / 2 * hrearrange)).resolve_left
        flowScale_ne_zero
    have hsnd : (familyField lam ε (a, a * t)).2 = 0 := by
      rw [ht₀, hfst, mul_zero, mul_zero, sub_zero] at ht
      exact (mul_eq_zero.mp ht).resolve_left flowScale_ne_zero
    exact Prod.ext hfst hsnd

/-- Weighted squared strength on the homogeneous coupling plane. -/
def weightedStrength (lam a b : ℝ) : ℝ := a ^ 2 + 3 * lam * b ^ 2

/-- Quartic damping of the weighted squared strength. -/
def radialDamping (lam a b : ℝ) : ℝ :=
  a ^ 4 + 6 * lam * (a * b - 2 * b ^ 2 / 3) ^ 2 + (3 * lam ^ 2 + 10 * lam / 3) * b ^ 4

theorem familyField_weightedStrength (lam ε a b : ℝ) :
    flowScale * (2 * a * (familyField lam ε (a, b)).1 +
      6 * lam * b * (familyField lam ε (a, b)).2) =
        flowScale * ε * weightedStrength lam a b - radialDamping lam a b := by
  rw [mul_add, mul_left_comm flowScale (2 * a), mul_left_comm flowScale (6 * lam * b),
    flowScale_mul_familyField_fst, flowScale_mul_familyField_snd]
  simp only [familyM, familyP, familyQ, weightedStrength, radialDamping, flowScale]
  ring

/-- A lower bound for radial damping that is uniform in positive `lam`. -/
theorem weightedStrength_sq_div_six_le_radialDamping {lam : ℝ} (hlam : 0 ≤ lam)
    (a b : ℝ) : weightedStrength lam a b ^ 2 / 6 ≤ radialDamping lam a b := by
  calc
    weightedStrength lam a b ^ 2 / 6 ≤ a ^ 4 + 3 * lam ^ 2 * b ^ 4 := by
      unfold weightedStrength
      nlinarith only [sq_nonneg (a ^ 2 - 3 * lam * b ^ 2), pow_nonneg (sq_nonneg a) 2]
    _ ≤ radialDamping lam a b := by
      unfold radialDamping
      have h₁ := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hlam)
        (sq_nonneg (a * b - 2 * b ^ 2 / 3))
      have h₂ := mul_nonneg hlam (pow_nonneg (sq_nonneg b) 2)
      nlinarith only [h₁, h₂]

/-- An upper bound for radial damping at both physical values of `lam`. -/
theorem radialDamping_le_three_weightedStrength_sq {lam : ℝ} (hlam : 1 / 2 ≤ lam)
    (a b : ℝ) : radialDamping lam a b ≤ 3 * weightedStrength lam a b ^ 2 := by
  have hnonneg : 0 ≤ lam := by linarith
  have hb4 : 0 ≤ b ^ 4 := by positivity
  calc
    radialDamping lam a b ≤ a ^ 4 + 12 * lam * a ^ 2 * b ^ 2 +
        (3 * lam ^ 2 + 26 * lam / 3) * b ^ 4 := by
      unfold radialDamping
      nlinarith only [mul_nonneg hnonneg (sq_nonneg (a * b + 2 * b ^ 2 / 3))]
    _ ≤ 3 * weightedStrength lam a b ^ 2 := by
      unfold weightedStrength
      have h₁ := mul_nonneg (mul_nonneg hnonneg (show 0 ≤ 2 * lam - 1 by linarith)) hb4
      have h₂ := mul_nonneg (sq_nonneg lam) hb4
      have h₃ : 0 ≤ lam * a ^ 2 * b ^ 2 := by positivity
      have h₄ : 0 ≤ a ^ 4 := by positivity
      nlinarith only [h₁, h₂, h₃, h₄]

end

end ThirteenPlanes
