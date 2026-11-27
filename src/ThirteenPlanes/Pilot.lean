module

public import ThirteenPlanes.Basins.Endpoints
public import ThirteenPlanes.Energy
public import ThirteenPlanes.FourPlanesTwoShare
public import ThirteenPlanes.ModelCoordinates
public import ThirteenPlanes.PilotContractions

@[expose] public section

/-! The eight-field control on the concrete matrix cubics and the three marked fields. -/

open Filter Set Topology

namespace ThirteenPlanes

noncomputable section

/-- The actual matrix control has the verified dimension, contractions and marked energy tests. -/
theorem fourPlane_pilot_contract :
    Module.finrank ℝ TracelessHermitian3 = 8 ∧
    HasContractionLaws fourPlanePair (1 / 2) ∧
    EnergyTests fourPlanePair fourPlaneMarkedOne fourPlaneMarkedTwo fourPlaneMarkedThree ∧
    LinearIndependent ℝ ![fourPlanePair.diagonalCubic, fourPlanePair.mixingCubic] :=
  ⟨fourPlane_dimension, fourPlane_contractionLaws, fourPlaneEnergyTests,
    modelCubics_independent fourPlaneEnergyTests⟩

/-- The tensor beta preserves the actual four-plane matrix family in physical time. -/
theorem fourPlane_oneLoop (ε : ℝ) (u : ℝ × ℝ) :
    oneLoopBeta ε (coupling fourPlanePair u) = coupling fourPlanePair (familyField (1 / 2) ε u) :=
  oneLoop_restricts_to_familyField fourPlanePair fourPlane_contractionLaws u

/-- A fixed point of the actual tensor field is a fixed point of its unique matrix-family coordinates. -/
theorem fourPlane_oneLoop_eq_zero_iff (ε : ℝ) (u : ℝ × ℝ) :
    oneLoopBeta ε (coupling fourPlanePair u) = 0 ↔ familyField (1 / 2) ε u = 0 := by
  rw [fourPlane_oneLoop, ← (coupling fourPlanePair).map_zero]
  exact (modelCoupling_injective fourPlaneEnergyTests).eq_iff

/-- The three fixed strengths in Proposition 5.1 on the actual traceless Hermitian cubics. -/
theorem fourPlane_tensor_fixed_table (ε a t : ℝ) (ha : a ≠ 0) :
    oneLoopBeta ε (coupling fourPlanePair (a, a * t)) = 0 ↔
      (t = 1 ∧ a ^ 2 / flowScale = 2 * ε / 3) ∨
      (t = -2 ∧ a ^ 2 / flowScale = ε / 15) ∨
      (t = 0 ∧ a ^ 2 / flowScale = ε) :=
  (fourPlane_oneLoop_eq_zero_iff ε _).trans (eight_fixed_iff ha)

/-- The matrix control realizes both signs at each of the three fixed ratios for positive `ε`. -/
theorem fourPlane_tensor_fixed_exists {ε t : ℝ} (hε : 0 < ε)
    (ht : t = 1 ∨ t = -2 ∨ t = 0) :
    ∃ a : ℝ, 0 < a ∧ oneLoopBeta ε (coupling fourPlanePair (a, a * t)) = 0 ∧
      oneLoopBeta ε (coupling fourPlanePair (-a, -a * t)) = 0 := by
  obtain ⟨a, ha, h₁, h₂⟩ := eight_fixed_exists_at_ratio hε ht
  exact ⟨a, ha, (fourPlane_oneLoop_eq_zero_iff ε _).mpr h₁,
    (fourPlane_oneLoop_eq_zero_iff ε _).mpr h₂⟩

/-- Each concrete fixed point has a triangular chart linearization with strength exponent `ε`. -/
theorem fourPlane_tensor_fixed_linearization {ε a t : ℝ} (ha : a ≠ 0)
    (h : oneLoopBeta ε (coupling fourPlanePair (a, a * t)) = 0) :
    HasDerivAt (fun x ↦ (chartField (1 / 2) ε (x, t)).1) (-ε) a ∧
    HasDerivAt (fun x ↦ (chartField (1 / 2) ε (x, t)).2) 0 a ∧
    HasDerivAt (fun x ↦ (chartField (1 / 2) ε (a, x)).2) (-ratioExponent (1 / 2) a t) t :=
  chartLinearization_at_fixed ha ((fourPlane_oneLoop_eq_zero_iff ε _).mp h)

/-- The ratio exponents and scalar field dimensions in Proposition 5.1. -/
theorem fourPlane_tensor_fixed_scaling {ε a t : ℝ} (ha : a ≠ 0)
    (h : oneLoopBeta ε (coupling fourPlanePair (a, a * t)) = 0) :
    (t = 1 ∧ ratioExponent (1 / 2) a t = ε ∧ scalarDimension (1 / 2) ε a t = 1 - 2 * ε / 9) ∨
    (t = -2 ∧ ratioExponent (1 / 2) a t = -2 * ε / 5 ∧
      scalarDimension (1 / 2) ε a t = 1 - 19 * ε / 45) ∨
    (t = 0 ∧ ratioExponent (1 / 2) a t = 0 ∧ scalarDimension (1 / 2) ε a t = 1 - ε / 3) :=
  eight_stationary_scaling ha ((fourPlane_oneLoop_eq_zero_iff ε _).mp h)

/-- Applying any linear functional to the matrix pencil recovers the tensor equation along a scalar solution. -/
theorem fourPlane_tensorFlow_iff {ε s : ℝ} (u : ℝ → ℝ × ℝ) :
    HasDerivAt u (familyField (1 / 2) ε (u s)) s ↔
      ∀ φ : SymmetricCubic TracelessHermitian3 →ₗ[ℝ] ℝ,
        HasDerivAt (fun r ↦ φ (coupling fourPlanePair (u r)))
          (φ (oneLoopBeta ε (coupling fourPlanePair (u s)))) s :=
  familyFlow_iff_tensorFlow fourPlanePair fourPlane_contractionLaws
    (modelCubics_independent fourPlaneEnergyTests) u s

/-- A nonzero initial coupling of the four-plane matrix family has a unique global forward
solution on its coefficient plane, and the limit represents a nonzero fixed tensor. -/
theorem fourPlane_tensor_forward_solution {ε : ℝ} (hε : 0 < ε)
    {u₀ : ℝ × ℝ} (hu₀ : u₀ ≠ 0) :
    ∃ u : ℝ → ℝ × ℝ, u 0 = u₀ ∧
      IsIntegralCurveOn u (fun _ ↦ familyField (1 / 2) ε) (Ici 0) ∧
      (∀ y : ℝ → ℝ × ℝ, y 0 = u₀ →
        IsIntegralCurveOn y (fun _ ↦ familyField (1 / 2) ε) (Ici 0) → EqOn y u (Ici 0)) ∧
      ∃ p : ℝ × ℝ, coupling fourPlanePair p ≠ 0 ∧
        oneLoopBeta ε (coupling fourPlanePair p) = 0 ∧ Tendsto u atTop (𝓝 p) := by
  obtain ⟨u, h0, hu, hunique, p, hp, hfixed, hlim⟩ :=
    existsUnique_forward_solution_tendsto_fixedPoint (lam := 1 / 2) le_rfl hε hu₀
  refine ⟨u, h0, hu, hunique, p, ?_, (fourPlane_oneLoop_eq_zero_iff ε p).mpr hfixed, hlim⟩
  intro hz
  apply hp
  exact modelCoupling_injective fourPlaneEnergyTests (by simpa only [map_zero] using hz)

/-- The two ratio intervals of Proposition 5.1 converge to the corresponding fixed strengths. -/
theorem fourPlane_tensor_basin_limits {ε : ℝ} (hε : 0 < ε) {u : ℝ → ℝ × ℝ}
    (hu : IsIntegralCurveOn u (fun _ ↦ familyField (1 / 2) ε) (Ici 0)) (ha : (u 0).1 ≠ 0) :
    (0 < (u 0).2 / (u 0).1 → (u 0).2 / (u 0).1 < 1 →
      Tendsto (fun s ↦ ((u s).1 ^ 2 / flowScale, (u s).2 / (u s).1)) atTop (𝓝 (2 * ε / 3, 1))) ∧
    (-2 < (u 0).2 / (u 0).1 → (u 0).2 / (u 0).1 < 0 →
      Tendsto (fun s ↦ ((u s).1 ^ 2 / flowScale, (u s).2 / (u s).1)) atTop (𝓝 (ε, 0))) :=
  ⟨eight_basin_equalStrength hε hu ha, eight_basin_decoupled hε hu ha⟩

end

end ThirteenPlanes
