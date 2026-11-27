module

public import ThirteenPlanes.Basins.Endpoints
public import ThirteenPlanes.Energy
public import ThirteenPlanes.ModelCoordinates
public import ThirteenPlanes.PlaneContractions
public import ThirteenPlanes.Potential
public import ThirteenPlanes.SignedEnergyShares
public import ThirteenPlanes.SignedTits

@[expose] public section

/-! The concrete 26-field one-loop pencil on the signed ternary carrier. -/

open Filter Set Topology

namespace ThirteenPlanes

noncomputable section

/-- The support, trace-free restrictions and transported Tits square give both contractions. -/
theorem signed_contractionLaws : HasContractionLaws signedPair 2 := by
  have h := planeContractionLaws signedPair signedPlaneDecomposition signedPair_hasPlaneData
    signedPair_hasSquareLaw
  rw [signedField_finrank] at h
  norm_num at h
  exact h

/-- The actual signed coordinate corners realize all three energy tests. -/
theorem signed_energyTests : EnergyTests signedPair signedMarkedOne signedMarkedTwo signedMarkedThree :=
  signedEnergyTests signedEqualCubic_hasSquareLaw

/-- The signed unit-sphere energy is direction independent exactly at `a = b`. -/
theorem signed_unitEnergy_constant_iff (u : ℝ × ℝ) :
    (∃ c, ConstantOnSphere (unitEnergy (coupling signedPair u)) c) ↔ u.1 = u.2 :=
  unitEnergy_constant_iff signed_energyTests u

/-- Proposition 3.2 on the actual signed carrier. -/
theorem signed_unitEnergy_constant_iff_mixingRatio_eq_one (t : ℝ) :
    (∃ c, ConstantOnSphere (unitEnergy (interactionCubic signedPair t)) c) ↔ t = 1 :=
  unitEnergy_constant_iff_mixingRatio_eq_one signed_energyTests t

theorem signed_unitEnergy_at_one :
    ConstantOnSphere (unitEnergy (interactionCubic signedPair 1)) 1 :=
  unitEnergy_interactionCubic_one signed_energyTests

/-- The two marked shares measure the mixing ratio. -/
theorem signed_mixingRatio_of_energies (t : ℝ) :
    t = 3 * unitEnergy (interactionCubic signedPair t) signedMarkedThree -
      2 * unitEnergy (interactionCubic signedPair t) signedMarkedTwo :=
  mixingRatio_eq_of_energies signed_energyTests t

/-- The weighted planar radius is the actual squared tensor norm, up to the factor `26/3`. -/
theorem signed_coupling_tensorPairing_self (u : ℝ × ℝ) :
    (coupling signedPair u).tensorPairing (coupling signedPair u) =
      (26 / 3 : ℝ) * weightedStrength 2 u.1 u.2 := by
  rw [SymmetricCubic.tensorPairing_self, signed_contractionLaws.double, map_smul,
    LinearMap.trace_id, signedField_finrank]
  simp only [smul_eq_mul, familyM, weightedStrength, Nat.cast_ofNat]
  ring

/-- The Gram coefficients of the signed diagonal and mixing tensors in Theorem 2.1. -/
theorem signed_tensor_gram :
    signedPair.diagonalCubic.tensorPairing signedPair.diagonalCubic = 26 / 3 ∧
    signedPair.mixingCubic.tensorPairing signedPair.mixingCubic = 52 ∧
    signedPair.diagonalCubic.tensorPairing signedPair.mixingCubic = 0 := by
  let D := signedPair.diagonalCubic
  let C := signedPair.mixingCubic
  have hD : D.tensorPairing D = 26 / 3 := by
    simpa [coupling_apply, weightedStrength] using signed_coupling_tensorPairing_self (1, 0)
  have hC : C.tensorPairing C = 52 := by
    have h := signed_coupling_tensorPairing_self (0, 1)
    norm_num [coupling_apply, weightedStrength] at h
    exact h
  have hsum : (D + C).tensorPairing (D + C) = 26 / 3 * 7 := by
    have h := signed_coupling_tensorPairing_self (1, 1)
    norm_num [coupling_apply, weightedStrength] at h ⊢
    exact h
  have hadd (x : SymmetricCubic SignedField) :
      (D + C).tensorPairing x = D.tensorPairing x + C.tensorPairing x := by
    rw [SymmetricCubic.tensorPairing_comm (D + C) x, SymmetricCubic.tensorPairing_add_right,
      SymmetricCubic.tensorPairing_comm x D, SymmetricCubic.tensorPairing_comm x C]
  rw [SymmetricCubic.tensorPairing_add_right, hadd D, hadd C,
    SymmetricCubic.tensorPairing_comm C D, hD, hC] at hsum
  exact ⟨hD, hC, by linarith [hsum]⟩

/-- The signed tensor beta restricts to the physical `lam = 2` planar equation. -/
theorem signed_oneLoop (ε : ℝ) (u : ℝ × ℝ) :
    oneLoopBeta ε (coupling signedPair u) = coupling signedPair (familyField 2 ε u) :=
  oneLoop_restricts_to_familyField signedPair signed_contractionLaws u

theorem signed_oneLoop_eq_zero_iff (ε : ℝ) (u : ℝ × ℝ) :
    oneLoopBeta ε (coupling signedPair u) = 0 ↔ familyField 2 ε u = 0 := by
  rw [signed_oneLoop, ← (coupling signedPair).map_zero]
  exact (modelCoupling_injective signed_energyTests).eq_iff

/-- The three non-Gaussian fixed strengths on the actual signed tensor pencil. -/
theorem signed_tensor_fixed_table (ε a t : ℝ) (ha : a ≠ 0) :
    oneLoopBeta ε (coupling signedPair (a, a * t)) = 0 ↔
      (t = 1 ∧ a ^ 2 / flowScale = ε / 3) ∨
      (t = -1 / 2 ∧ a ^ 2 / flowScale = ε / 3) ∨
      (t = 0 ∧ a ^ 2 / flowScale = ε) :=
  (signed_oneLoop_eq_zero_iff ε _).trans (twentySix_fixed_iff ha)

theorem signed_tensor_fixed_exists {ε t : ℝ} (hε : 0 < ε) (ht : t = 1 ∨ t = -1 / 2 ∨ t = 0) :
    ∃ a : ℝ, 0 < a ∧ oneLoopBeta ε (coupling signedPair (a, a * t)) = 0 ∧
      oneLoopBeta ε (coupling signedPair (-a, -a * t)) = 0 := by
  obtain ⟨a, ha, h₁, h₂⟩ := twentySix_fixed_exists_at_ratio hε ht
  exact ⟨a, ha, (signed_oneLoop_eq_zero_iff ε _).mpr h₁, (signed_oneLoop_eq_zero_iff ε _).mpr h₂⟩

theorem signed_tensor_fixed_linearization {ε a t : ℝ} (ha : a ≠ 0)
    (h : oneLoopBeta ε (coupling signedPair (a, a * t)) = 0) :
    HasDerivAt (fun x ↦ (chartField 2 ε (x, t)).1) (-ε) a ∧
    HasDerivAt (fun x ↦ (chartField 2 ε (x, t)).2) 0 a ∧
    HasDerivAt (fun x ↦ (chartField 2 ε (a, x)).2) (-ratioExponent 2 a t) t :=
  chartLinearization_at_fixed ha ((signed_oneLoop_eq_zero_iff ε _).mp h)

theorem signed_tensor_fixed_scaling {ε a t : ℝ} (ha : a ≠ 0)
    (h : oneLoopBeta ε (coupling signedPair (a, a * t)) = 0) :
    (t = 1 ∧ ratioExponent 2 a t = ε ∧ scalarDimension 2 ε a t = 1 - ε / 9) ∨
    (t = -1 / 2 ∧ ratioExponent 2 a t = -ε / 4 ∧
      scalarDimension 2 ε a t = 1 - 13 * ε / 36) ∨
    (t = 0 ∧ ratioExponent 2 a t = 0 ∧ scalarDimension 2 ε a t = 1 - ε / 3) :=
  twentySix_stationary_scaling ha ((signed_oneLoop_eq_zero_iff ε _).mp h)

/-- Linear readings of the concrete signed tensor solve the tensor equation exactly along
solutions of its scalar coefficient equation. -/
theorem signed_tensorFlow_iff {ε s : ℝ} (u : ℝ → ℝ × ℝ) :
    HasDerivAt u (familyField 2 ε (u s)) s ↔
      ∀ φ : SymmetricCubic SignedField →ₗ[ℝ] ℝ,
        HasDerivAt (fun r ↦ φ (coupling signedPair (u r)))
          (φ (oneLoopBeta ε (coupling signedPair (u s)))) s :=
  familyFlow_iff_tensorFlow signedPair signed_contractionLaws
    (modelCubics_independent signed_energyTests) u s

/-- Every nonzero signed coupling has a unique global forward coefficient solution and a nonzero
fixed tensor at its limit. -/
theorem signed_tensor_forward_solution {ε : ℝ} (hε : 0 < ε)
    {u₀ : ℝ × ℝ} (hu₀ : u₀ ≠ 0) :
    ∃ u : ℝ → ℝ × ℝ, u 0 = u₀ ∧ IsIntegralCurveOn u (fun _ ↦ familyField 2 ε) (Ici 0) ∧
      (∀ y : ℝ → ℝ × ℝ, y 0 = u₀ →
        IsIntegralCurveOn y (fun _ ↦ familyField 2 ε) (Ici 0) → EqOn y u (Ici 0)) ∧
      ∃ p : ℝ × ℝ, coupling signedPair p ≠ 0 ∧
        oneLoopBeta ε (coupling signedPair p) = 0 ∧ Tendsto u atTop (𝓝 p) := by
  obtain ⟨u, h0, hu, hunique, p, hp, hfixed, hlim⟩ :=
    existsUnique_forward_solution_tendsto_fixedPoint (lam := 2) (by norm_num) hε hu₀
  refine ⟨u, h0, hu, hunique, p, ?_, (signed_oneLoop_eq_zero_iff ε p).mpr hfixed, hlim⟩
  intro hz
  apply hp
  exact modelCoupling_injective signed_energyTests (by simpa only [map_zero] using hz)

/-- The squared tensor norm remains in a positive bounded interval along each nonzero forward orbit. -/
theorem signed_tensor_strength_bounds {ε : ℝ} (hε : 0 < ε) {u : ℝ → ℝ × ℝ}
    (hu : IsIntegralCurveOn u (fun _ ↦ familyField 2 ε) (Ici 0)) (h0 : u 0 ≠ 0) :
    ∃ r R : ℝ, 0 < r ∧ ∀ t, 0 ≤ t →
      r ≤ (coupling signedPair (u t)).tensorPairing (coupling signedPair (u t)) ∧
      (coupling signedPair (u t)).tensorPairing (coupling signedPair (u t)) ≤ R := by
  obtain ⟨r, R, hr, hb⟩ := twentySix_strength_bounds hε hu h0
  refine ⟨(26 / 3 : ℝ) * r, (26 / 3 : ℝ) * R, by positivity, ?_⟩
  intro t ht
  rw [signed_coupling_tensorPairing_self]
  exact ⟨mul_le_mul_of_nonneg_left (hb t ht).1 (by norm_num),
    mul_le_mul_of_nonneg_left (hb t ht).2 (by norm_num)⟩

/-- Squared tensor distance in the concrete signed coupling plane. -/
def signedTensorDistanceSq (u v : ℝ × ℝ) : ℝ :=
  let d := coupling signedPair u - coupling signedPair v
  d.tensorPairing d

theorem signedTensorDistanceSq_tendsto {u : ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    (hu : Tendsto u atTop (𝓝 p)) : Tendsto (fun s ↦ signedTensorDistanceSq (u s) p) atTop (𝓝 0) := by
  let f : ℝ × ℝ → ℝ := fun v ↦ (26 / 3 : ℝ) * weightedStrength 2 (v.1 - p.1) (v.2 - p.2)
  have hf : Continuous f := by
    unfold f weightedStrength
    fun_prop
  have hf0 : f p = 0 := by simp [f, weightedStrength]
  have h : Tendsto (fun s ↦ f (u s)) atTop (𝓝 0) := hf0 ▸ (hf.tendsto p).comp hu
  convert h using 1
  funext s
  have hm : coupling signedPair (u s - p) = coupling signedPair (u s) - coupling signedPair p := by
    apply SymmetricCubic.ext
    intro x y z
    simp only [coupling_apply, Prod.fst_sub, Prod.snd_sub, SymmetricCubic.apply_sub',
      SymmetricCubic.apply_add, SymmetricCubic.apply_smul]
    ring
  rw [signedTensorDistanceSq, ← hm, signed_coupling_tensorPairing_self]
  rfl

/-- The `t = 1` basin has the signed limiting tensor selected by the initial sign of `b`.
Below the separating ratio it also crosses the pure-mixing axis in finite positive time. -/
theorem signed_tensor_basin_equalStrength {ε : ℝ} (hε : 0 < ε) {u : ℝ → ℝ × ℝ}
    (hu : IsIntegralCurveOn u (fun _ ↦ familyField 2 ε) (Ici 0)) (hb : (u 0).2 ≠ 0)
    (hchart : (u 0).1 = 0 ∨ (u 0).2 / (u 0).1 ∉ Icc (-1 / 2) 0) :
    Tendsto (fun s ↦ (u s).2 / (u s).1) atTop (𝓝 1) ∧
    Tendsto (fun s ↦ (u s).1 ^ 2 / flowScale) atTop (𝓝 (ε / 3)) ∧
    (0 < (u 0).2 → Tendsto (fun s ↦ signedTensorDistanceSq (u s)
      (equalStrengthLevel 2 ε, equalStrengthLevel 2 ε)) atTop (𝓝 0)) ∧
    ((u 0).2 < 0 → Tendsto (fun s ↦ signedTensorDistanceSq (u s)
      (-equalStrengthLevel 2 ε, -equalStrengthLevel 2 ε)) atTop (𝓝 0)) ∧
    ((u 0).1 ≠ 0 → (u 0).2 / (u 0).1 < -1 / 2 → ∃ s, 0 < s ∧ (u s).1 = 0) := by
  obtain ⟨hr, hg, hp, hn, hc⟩ := twentySix_basin_equalStrength hε hu hb hchart
  exact ⟨hr, hg, fun hs ↦ signedTensorDistanceSq_tendsto (hp hs),
    fun hs ↦ signedTensorDistanceSq_tendsto (hn hs), hc⟩

/-- The open decoupled basin converges in the tensor norm to the fixed point with the initial sign of `a`. -/
theorem signed_tensor_basin_decoupled {ε : ℝ} (hε : 0 < ε) {u : ℝ → ℝ × ℝ}
    (hu : IsIntegralCurveOn u (fun _ ↦ familyField 2 ε) (Ici 0)) (ha : (u 0).1 ≠ 0)
    (hlo : -1 / 2 < (u 0).2 / (u 0).1) (hhi : (u 0).2 / (u 0).1 < 0) :
    Tendsto (fun s ↦ (u s).2 / (u s).1) atTop (𝓝 0) ∧
    Tendsto (fun s ↦ (u s).1 ^ 2 / flowScale) atTop (𝓝 ε) ∧
    (0 < (u 0).1 → Tendsto (fun s ↦ signedTensorDistanceSq (u s) (decoupledLevel ε, 0)) atTop (𝓝 0)) ∧
    ((u 0).1 < 0 → Tendsto (fun s ↦ signedTensorDistanceSq (u s) (-decoupledLevel ε, 0)) atTop (𝓝 0)) := by
  obtain ⟨hr, hg, hp, hn⟩ := twentySix_basin_decoupled hε hu ha hlo hhi
  exact ⟨hr, hg, fun hs ↦ signedTensorDistanceSq_tendsto (hp hs),
    fun hs ↦ signedTensorDistanceSq_tendsto (hn hs)⟩

/-- Pure mixing is not a fixed tensor except at the Gaussian origin. -/
theorem signed_oneLoop_pureMixing_ne_zero (ε : ℝ) {b : ℝ} (hb : b ≠ 0) :
    oneLoopBeta ε (coupling signedPair (0, b)) ≠ 0 := by
  intro h
  exact familyField_pureMixing_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hb
    ((signed_oneLoop_eq_zero_iff ε (0, b)).mp h)

end

end ThirteenPlanes
