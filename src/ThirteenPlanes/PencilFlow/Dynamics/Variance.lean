module

public import ThirteenPlanes.PencilFlow.Dynamics.Physical
public import ThirteenPlanes.PencilFlow.Pencil.Floor
public import ThirteenPlanes.FamilyVariance.Descent

@[expose] public section

/-! The spherical variance and potential (c): the relative variance is invariant under rescaling, and it
decreases strictly along the flow off the fixed ratios. The pencil `P` at strength `c`, rescaled
by `σ⁻¹`, `σ² = 6c`, satisfies the contraction laws `HasContractionLaws`, so the explicit variance formula and descent rate apply. -/

open Filter Set
open scoped Topology

namespace ThirteenPlanes.PencilFlow.Dynamics

noncomputable section

open Statements ThirteenPlanes SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem fieldEnergy_smul (k : ℝ) (h : SymmetricCubic V) :
    fieldEnergy (k • h) = fun x => k ^ 2 * fieldEnergy h x := by
  funext x
  simp only [fieldEnergy, squareMap_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The relative variance is invariant under nonzero rescaling. -/
theorem relativeVariance_smul {k : ℝ} (hk : k ≠ 0) (h : SymmetricCubic V) :
    relativeVariance (k • h) = relativeVariance h := by
  unfold relativeVariance sphereVariance
  rw [fieldEnergy_smul, sphereAverage_const_mul]
  have e : (fun x => (k ^ 2 * fieldEnergy h x - k ^ 2 * sphereAverage (fieldEnergy h)) ^ 2) =
      fun x => (k ^ 2) ^ 2 * (fieldEnergy h x - sphereAverage (fieldEnergy h)) ^ 2 := by
    funext x; ring
  rw [e, sphereAverage_const_mul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (pow_ne_zero 2 hk))

/-- The pencil rescaled to the trace normalization. -/
def scaledPair (σ : ℝ) (P : CubicPair V) : CubicPair V :=
  ⟨σ⁻¹ • P.diagonalCubic, σ⁻¹ • P.mixingCubic⟩

omit [FiniteDimensional ℝ V] in
theorem coupling_scaledPair (σ : ℝ) (P : CubicPair V) (u : ℝ × ℝ) :
    coupling (scaledPair σ P) u = coupling P (σ⁻¹ • u) := by
  simp only [coupling_apply, scaledPair, smul_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_comm]

variable {m : ℕ} {h : SymmetricCubic V} {c : ℝ} {planes : PlaneDecomposition V (Fin m)}

/-- The rescaled closed pencil satisfies the contraction laws. -/
theorem scaledPair_laws {σ : ℝ} (hσ0 : σ ≠ 0) (hσ : σ ^ 2 = 6 * c) (hround : IsRound h c)
    (hclosed : IsClosedPlaneSystem h planes) :
    HasContractionLaws (scaledPair σ (planePencil h planes)) (pencilLambda V) := by
  have hc6 : c = σ ^ 2 / 6 := by linarith
  constructor
  · rintro ⟨a, b⟩
    rw [coupling_scaledPair]
    have := (Pencil.closedPencil_contractions h c planes hround hclosed (σ⁻¹ * a) (σ⁻¹ * b)).1
    simp only [Prod.smul_mk, smul_eq_mul]
    rw [this]
    congr 1
    simp only [familyM]
    rw [hc6]
    field_simp
    ring
  · rintro ⟨a, b⟩
    rw [coupling_scaledPair, coupling_scaledPair]
    have := (Pencil.closedPencil_contractions h c planes hround hclosed (σ⁻¹ * a) (σ⁻¹ * b)).2
    simp only [Prod.smul_mk, smul_eq_mul]
    rw [this, coupling_apply]
    simp only
    have e1 : -3 * c * pencilLambda V * (σ⁻¹ * b) ^ 3 = σ⁻¹ * familyP (pencilLambda V) (a, b) := by
      simp only [familyP]; rw [hc6]; field_simp; ring
    have e2 : -3 * c * (σ⁻¹ * b) ^ 2 * (σ⁻¹ * a - σ⁻¹ * b + pencilLambda V * (σ⁻¹ * b)) =
        σ⁻¹ * familyQ (pencilLambda V) (a, b) := by
      simp only [familyQ]; rw [hc6]; field_simp; ring
    rw [e1, e2]

theorem scaledPair_traceFree (σ : ℝ) (hround : IsRound h c)
    (hclosed : IsClosedPlaneSystem h planes) :
    (scaledPair σ (planePencil h planes)).diagonalCubic.TraceFree ∧
      (scaledPair σ (planePencil h planes)).mixingCubic.TraceFree := by
  obtain ⟨hD, hC⟩ := Pencil.closedPencil_traceFree hround hclosed
  refine ⟨fun x => ?_, fun x => ?_⟩
  · change LinearMap.trace ℝ V ((σ⁻¹ • (planePencil h planes).diagonalCubic).L x) = 0
    rw [map_smul, LinearMap.smul_apply, map_smul, hD x, smul_zero]
  · change LinearMap.trace ℝ V ((σ⁻¹ • (planePencil h planes).mixingCubic).L x) = 0
    rw [map_smul, LinearMap.smul_apply, map_smul, hC x, smul_zero]

end

end ThirteenPlanes.PencilFlow.Dynamics

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements Dynamics ThirteenPlanes

/-- The spherical variance and potential (c), invariance under rescaling and strict descent. -/
theorem relativeVarianceDescent (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.VarianceC V := by
  intro m hm h c planes hround hclosed ε hε u s hg hd
  dsimp only
  have hc := hround.positive
  have hlam := pencilLambda_pos hm planes
  have h4 := four_le_finrank hm planes
  have h4' : 0 < Module.finrank ℝ V := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos h4'
  set P := planePencil h planes
  set σ := Real.sqrt (6 * c)
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσ : σ ^ 2 = 6 * c := Real.sq_sqrt (by positivity)
  have hα : (4 * Real.pi * Real.sqrt ε)⁻¹ ≠ 0 := by
    have := Real.sqrt_pos.mpr hε
    have := Real.pi_pos
    positivity
  refine ⟨?_, fun hrate => ?_⟩
  · have e : coupling P (u s) = (u s).1 • interactionCubic P ((u s).2 / (u s).1) := by
      simp only [interactionCubic, coupling_apply, smul_add, smul_smul, one_smul]
      rw [mul_div_cancel₀ _ hg]
    rw [e, smul_smul, relativeVariance_smul (mul_ne_zero hα hg)]
  · obtain ⟨hD, hC⟩ := scaledPair_traceFree σ hround hclosed
    have hlaws := scaledPair_laws hσ0.ne' hσ hround hclosed
    have hfun : (fun r => relativeVariance ((4 * Real.pi * Real.sqrt ε)⁻¹ • coupling P (u r))) =
        fun r => anisotropyRational (Module.finrank ℝ V) (pencilLambda V) (σ • u r) := by
      funext r
      rw [relativeVariance_smul hα, ← familyAnisotropy_eq hlaws hD hC, familyAnisotropy,
        coupling_scaledPair, inv_smul_smul₀ hσ0.ne']
    rw [hfun]
    have hu : HasDerivWithinAt u (physicalCoefficientField c (pencilLambda V) ε (u s)) univ s :=
      coeff_deriv_of_tensor hm hround hclosed ε (hasDerivWithinAt_univ.mpr hd)
    have hw : HasDerivWithinAt (fun r => σ • u r)
        (familyField (pencilLambda V) ε (σ • u s)) univ s := by
      rw [familyField_smul hσ]; exact hu.const_smul σ
    have hws : σ • u s ≠ 0 := by
      intro h0
      have := congrArg Prod.fst h0
      simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_zero] at this
      exact hg ((mul_eq_zero.mp this).resolve_left hσ0.ne')
    have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast (by omega : 0 < Module.finrank ℝ V)
    refine ⟨_, ?_, (anisotropyRational_hasDerivWithinAt_flow hn hlam hw hws).hasDerivAt
      Filter.univ_mem⟩
    rw [anisotropyFlowRate_neg_iff hn hlam hws]
    intro hst
    apply hrate
    rw [ratioRate_eq_zero_iff hc hlam.ne' hg]
    simp only [StationaryRatio, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hst
    rcases hst with h1 | h1 | h1
    · left
      rw [(mul_eq_zero.mp h1).resolve_left hσ0.ne', zero_div]
    · right; left
      rw [mul_left_cancel₀ hσ0.ne' h1, div_self (by rw [← mul_left_cancel₀ hσ0.ne' h1]; exact hg)]
    · right; right
      have h2 : (u s).1 = -pencilLambda V * (u s).2 := by
        have := mul_left_cancel₀ hσ0.ne' (show σ * (u s).1 = σ * (-pencilLambda V * (u s).2) by
          rw [h1]; ring)
        exact this
      have hb : (u s).2 ≠ 0 := by
        intro hb; rw [hb, mul_zero] at h2; exact hg h2
      rw [h2]
      field_simp

end ThirteenPlanes.PencilFlow.Proofs
