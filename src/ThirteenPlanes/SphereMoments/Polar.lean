module

public import ThirteenPlanes.SphereMoments.Gaussian
public import Mathlib.MeasureTheory.Integral.Gamma

@[expose] public section

/-!
# Polar coordinates for homogeneous functions

The Gaussian integral of a function homogeneous of degree `d` factors as its integral over the unit
sphere (surface measure induced from Lebesgue measure) times a radial Gamma integral.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

/-- The radial integral `∫₀^∞ r^k exp(-r²) dr`. -/
def radialMoment (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * Real.exp (-r ^ 2)

theorem radialMoment_eq_gamma (k : ℕ) :
    radialMoment k = (1 / 2) * Real.Gamma ((k + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (k : ℝ)) two_pos
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  rw [radialMoment, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp [Real.rpow_natCast]

theorem radialMoment_pos (k : ℕ) : 0 < radialMoment k := by
  rw [radialMoment_eq_gamma]
  exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by positivity))

theorem radialMoment_add_two (k : ℕ) :
    radialMoment (k + 2) = (k + 1) / 2 * radialMoment k := by
  rw [radialMoment_eq_gamma, radialMoment_eq_gamma,
    show ((k + 2 : ℕ) + 1 : ℝ) / 2 = (k + 1) / 2 + 1 by push_cast; ring,
    Real.Gamma_add_one (by positivity)]
  ring

theorem radialMoment_add_two_mul (k m : ℕ) :
    radialMoment (k + 2 * m) =
      radialMoment k * ∏ j ∈ Finset.range m, ((k + 1 + 2 * j : ℝ) / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k + 2 * (m + 1) = (k + 2 * m) + 2 by ring, radialMoment_add_two, ih,
      Finset.prod_range_succ]
    push_cast
    ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Polar coordinates: the Gaussian integral of a function homogeneous of degree `d` is its
integral over the unit sphere times the radial moment of order `dim V - 1 + d`. -/
theorem gaussIntegral_of_homogeneous {f : V → ℝ} {d : ℕ}
    (hf : ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = r ^ d * f x) :
    gaussIntegral f = (∫ u, f u ∂(volume : Measure V).toSphere) *
      radialMoment (Module.finrank ℝ V - 1 + d) := by
  set n := Module.finrank ℝ V
  let G : Metric.sphere (0 : V) 1 × Ioi (0 : ℝ) → ℝ := fun p =>
    f p.1 * ((p.2 : ℝ) ^ d * Real.exp (-(p.2 : ℝ) ^ 2))
  have hG : ∀ x : ({0}ᶜ : Set V), G (homeomorphUnitSphereProd V x) = f x * gaussWeight (x : V) := by
    rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := hx
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    simp only [G, homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe,
      gaussWeight]
    have : f x = ‖x‖ ^ d * f (‖x‖⁻¹ • x) := by
      rw [← hf _ hn, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [this]; ring
  calc gaussIntegral f = ∫ x : ({0}ᶜ : Set V), f x * gaussWeight (x : V)
        ∂(Measure.comap Subtype.val volume) := by
          rw [integral_subtype_comap (measurableSet_singleton _).compl
            (fun x => f x * gaussWeight x), restrict_compl_singleton]
          rfl
    _ = ∫ p, G p ∂((volume : Measure V).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
          simp_rw [← hG]
          exact (volume : Measure V).measurePreserving_homeomorphUnitSphereProd.integral_comp
            (Homeomorph.measurableEmbedding _) G
    _ = (∫ u, f u ∂(volume : Measure V).toSphere) *
          ∫ r, (r : ℝ) ^ d * Real.exp (-(r : ℝ) ^ 2) ∂(Measure.volumeIoiPow (n - 1)) :=
          integral_prod_mul (fun u : Metric.sphere (0 : V) 1 => f u)
            (fun r : Ioi (0 : ℝ) => (r : ℝ) ^ d * Real.exp (-(r : ℝ) ^ 2))
    _ = _ := by
          congr 1
          simp only [Measure.volumeIoiPow, ENNReal.ofReal]
          rw [integral_withDensity_eq_integral_smul
              (measurable_subtype_coe.pow_const _).real_toNNReal,
            integral_subtype_comap measurableSet_Ioi
              (fun a : ℝ => Real.toNNReal (a ^ (n - 1)) • (a ^ d * Real.exp (-a ^ 2))),
            radialMoment]
          refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
          rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _), smul_eq_mul,
            pow_add]
          ring

/-- The total Gaussian mass in polar coordinates. -/
theorem gaussIntegral_one :
    gaussIntegral (fun _ : V => (1 : ℝ)) =
      (volume : Measure V).toSphere.real univ * radialMoment (Module.finrank ℝ V - 1) := by
  have h := gaussIntegral_of_homogeneous (f := fun _ : V => (1 : ℝ)) (d := 0) (by simp)
  simpa using h

end

end ThirteenPlanes
