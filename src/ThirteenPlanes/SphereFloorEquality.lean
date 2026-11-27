module

public import ThirteenPlanes.SphereFloor
public import ThirteenPlanes.AllCubicSquares

@[expose] public section

set_option backward.privateInPublic true

/-!
# Equality case of the floor identity

For a trace-free real symmetric cubic `κ` with scalar double contraction, `A(κ) ≥ A* = -x*/8`, with
equality exactly when `x = ⟨κ,κ⟩ = x*` and the field energy `U_κ = ‖Q_κ‖²/8` is the same in every
direction, i.e. constant on the unit sphere. The variance of `U_κ` over the unit sphere is
nonnegative and vanishes exactly when `U_κ` is constant there.
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]

open SymmetricCubic

/-- Under the hypotheses of the floor identity, `S - λΠ` with `λ = 2m/(N+2)` is trace-free. -/
private theorem harmonic_traceFree (κ : SymmetricCubic V) (hv : κ.TraceFree) {m : ℝ}
    (hM : κ.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) :
    IsTraceFree4 fun a b c d => κ.symmetrizedArray (stdOrthonormalBasis ℝ V) a b c d -
      2 * m / (Module.finrank ℝ V + 2) * pairingArray a b c d := by
  set N : ℝ := (Module.finrank ℝ V : ℝ)
  have hN : (0 : ℝ) < N := by simp only [N]; exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (Fin (Module.finrank ℝ V)) : ℝ) = N := by simp [N]
  intro c d
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    symmetrizedArray_trace (stdOrthonormalBasis ℝ V) κ hv m hM, pairingArray_trace, hcard]
  field_simp
  ring

/-- The sphere variance of the field energy is nonnegative, and it vanishes exactly when the field
energy is constant on the unit sphere (trace-free cubic with scalar double contraction). -/
theorem sphereVariance_energy_nonneg_and_eq_zero_iff (κ : SymmetricCubic V) (hv : κ.TraceFree)
    (hM : ∃ m : ℝ, κ.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) :
    0 ≤ sphereVariance (fun φ => ‖κ.squareMap φ‖ ^ 2 / 8) ∧
      (sphereVariance (fun φ => ‖κ.squareMap φ‖ ^ 2 / 8) = 0 ↔
        ∃ c : ℝ, ∀ φ : V, ‖φ‖ = 1 → ‖κ.squareMap φ‖ ^ 2 / 8 = c) := by
  obtain ⟨m, hM⟩ := hM
  set e := stdOrthonormalBasis ℝ V
  set lam : ℝ := 2 * m / (Module.finrank ℝ V + 2)
  set H := fun a b c d => κ.symmetrizedArray e a b c d - lam * pairingArray a b c d
  have hH : IsTraceFree4 H := harmonic_traceFree κ hv hM
  have hVar := sphereVariance_energy_of_traceFree e κ lam hH
  have hN : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  have hsq : ∑ a, ∑ b, ∑ c, ∑ d, (κ.symmetrizedArray e a b c d - lam * pairingArray a b c d) ^ 2 =
      Quartic.qinner H H := by
    simp only [Quartic.qinner, H, sq]
  rw [hsq] at hVar
  have hK : (0 : ℝ) < 24 * (Module.finrank ℝ V * (Module.finrank ℝ V + 2) *
      (Module.finrank ℝ V + 4) * (Module.finrank ℝ V + 6)) := by positivity
  refine ⟨by rw [hVar]; exact div_nonneg (Quartic.qinner_self_nonneg H) hK.le, ?_⟩
  constructor
  · intro h0
    rw [hVar, div_eq_zero_iff, or_iff_left hK.ne', Quartic.qinner_self_eq_zero] at h0
    refine ⟨lam / 8, fun φ hφ => ?_⟩
    rw [energy_eq_on_sphere e κ lam φ hφ]
    have : quarticForm e (fun a b d f => κ.symmetrizedArray e a b d f - lam * pairingArray a b d f)
        φ = 0 := by
      change quarticForm e H φ = 0
      rw [h0]; simp [quarticForm]
    rw [this]; ring
  · rintro ⟨c, hc⟩
    unfold sphereVariance
    have havg : sphereAverage (fun φ => ‖κ.squareMap φ‖ ^ 2 / 8) = c := by
      rw [sphereAverage_congr_sphere (g := fun _ => c) hc, sphereAverage_const]
    rw [havg, sphereAverage_congr_sphere (g := fun _ => (0 : ℝ))
      (fun φ hφ => by simp only; rw [hc φ hφ]; ring), sphereAverage_const]

/-- **Floor inequality and its equality case.** For a real symmetric cubic `κ` in `N ≥ 1`
variables with vanishing trace vector and scalar double contraction, `A(κ) ≥ A* = -x*/8`, with
equality exactly when `⟨κ,κ⟩ = x* = N(N+2)/(N+10)` and the field energy `‖Q_κ(φ)‖²/8` is the same
at every unit vector `φ`. -/
theorem aFunction_floor_equality (κ : SymmetricCubic V) (hv : κ.TraceFree)
    (hM : ∃ m : ℝ, κ.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) :
    let N : ℝ := Module.finrank ℝ V
    let xStar := N * (N + 2) / (N + 10)
    aFunction κ ≥ -xStar / 8 ∧
      (aFunction κ = -xStar / 8 ↔
        κ.tensorPairing κ = xStar ∧
          ∃ c : ℝ, ∀ φ : V, ‖φ‖ = 1 → ‖κ.squareMap φ‖ ^ 2 / 8 = c) := by
  intro N xStar
  have key := aFunction_floor_identity κ hv hM
  simp only at key
  obtain ⟨hnn, hiff⟩ := sphereVariance_energy_nonneg_and_eq_zero_iff κ hv hM
  set Vr := sphereVariance (fun φ => ‖κ.squareMap φ‖ ^ 2 / 8)
  have hN : (0 : ℝ) < N := by simp only [N]; exact_mod_cast Module.finrank_pos
  have hc : 0 < (N + 10) / (8 * N * (N + 2)) := by positivity
  have hK : 0 < 2 * N * (N + 2) * (N + 4) * (N + 6) := by positivity
  have hsq : 0 ≤ (κ.tensorPairing κ - xStar) ^ 2 := sq_nonneg _
  have t1 : 0 ≤ (N + 10) / (8 * N * (N + 2)) * (κ.tensorPairing κ - xStar) ^ 2 :=
    mul_nonneg hc.le hsq
  have t2 : 0 ≤ 2 * N * (N + 2) * (N + 4) * (N + 6) * Vr := mul_nonneg hK.le hnn
  refine ⟨by linarith, ?_⟩
  rw [← hiff]
  constructor
  · intro hA
    have hsum : (N + 10) / (8 * N * (N + 2)) * (κ.tensorPairing κ - xStar) ^ 2 +
        2 * N * (N + 2) * (N + 4) * (N + 6) * Vr = 0 := by rw [← key, hA]; ring
    have h1 : (N + 10) / (8 * N * (N + 2)) * (κ.tensorPairing κ - xStar) ^ 2 = 0 := by linarith
    have h2 : 2 * N * (N + 2) * (N + 4) * (N + 6) * Vr = 0 := by linarith
    refine ⟨?_, (mul_eq_zero.mp h2).resolve_left hK.ne'⟩
    have := (mul_eq_zero.mp h1).resolve_left hc.ne'
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · rintro ⟨hx, hV⟩
    have : aFunction κ - -xStar / 8 = 0 := by rw [key, hx, hV]; ring
    linarith

end

end ThirteenPlanes
