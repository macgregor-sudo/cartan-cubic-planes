module

public import ThirteenPlanes.PencilFlow.Dynamics.Planes
public import ThirteenPlanes.PencilFlow.Dynamics.Basin
public import ThirteenPlanes.PencilFlow.Pencil.Tangency

@[expose] public section

/-! The physical coefficient field is `familyField` after the rescaling `w = √(6c) u`.
Tangency and injectivity of the coupling map identify the tensor and coefficient equations. -/

open Filter Set
open scoped Topology

namespace ThirteenPlanes.PencilFlow.Dynamics

noncomputable section

open Statements

/-- Rescaling: `familyField lam ε (σ u) = σ · physicalCoefficientField c lam ε u` when
`σ² = 6c`. -/
theorem familyField_smul {c σ : ℝ} (hσ : σ ^ 2 = 6 * c) (lam ε : ℝ) (u : ℝ × ℝ) :
    familyField lam ε (σ • u) = σ • physicalCoefficientField c lam ε u := by
  have hc : c = σ ^ 2 / 6 := by linarith
  subst hc
  rcases u with ⟨a, b⟩
  ext <;> simp only [familyField, familyM, familyP, familyQ, physicalCoefficientField,
    Prod.smul_mk, smul_eq_mul] <;> ring

/-- A solution of the physical coefficient field, rescaled, solves the normalized coefficient field. -/
theorem integralCurve_scale {c σ : ℝ} (hσ : σ ^ 2 = 6 * c) {lam ε : ℝ} {u : ℝ → ℝ × ℝ}
    {S : Set ℝ} (hu : IsIntegralCurveOn u (fun _ => physicalCoefficientField c lam ε) S) :
    IsIntegralCurveOn (fun s => σ • u s) (fun _ => familyField lam ε) S := by
  intro s hs
  show HasDerivWithinAt _ (familyField lam ε (σ • u s)) S s
  rw [familyField_smul hσ]
  exact (hu s hs).const_smul σ

theorem integralCurve_unscale {c σ : ℝ} (hσ : σ ^ 2 = 6 * c) (hσ0 : σ ≠ 0) {lam ε : ℝ}
    {w : ℝ → ℝ × ℝ} {S : Set ℝ} (hw : IsIntegralCurveOn w (fun _ => familyField lam ε) S) :
    IsIntegralCurveOn (fun s => σ⁻¹ • w s) (fun _ => physicalCoefficientField c lam ε) S := by
  intro s hs
  show HasDerivWithinAt _ (physicalCoefficientField c lam ε (σ⁻¹ • w s)) S s
  have h : HasDerivWithinAt (fun s => σ⁻¹ • w s) (σ⁻¹ • familyField lam ε (w s)) S s :=
    (hw s hs).const_smul σ⁻¹
  have e : familyField lam ε (w s) = σ • physicalCoefficientField c lam ε (σ⁻¹ • w s) := by
    rw [← familyField_smul hσ, smul_inv_smul₀ hσ0]
  rw [e, inv_smul_smul₀ hσ0] at h
  exact h

/-- Derivatives can be pulled back through an injective linear map. -/
theorem hasDerivWithinAt_of_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E →ₗ[ℝ] F} (hf : Function.Injective f) {u : ℝ → E} {v : E} {S : Set ℝ} {s : ℝ}
    (hd : HasDerivWithinAt (fun r => f (u r)) (f v) S s) : HasDerivWithinAt u v S s := by
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have h := (LinearMap.toContinuousLinearMap g).hasFDerivAt.comp_hasDerivWithinAt s hd
  have e : ∀ x, g (f x) = x := fun x => by rw [← LinearMap.comp_apply, hg]; rfl
  simpa [Function.comp_def, e] using h

theorem hasDerivWithinAt_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ₗ[ℝ] F) {u : ℝ → E} {v : E} {S : Set ℝ} {s : ℝ}
    (hd : HasDerivWithinAt u v S s) : HasDerivWithinAt (fun r => f (u r)) (f v) S s := by
  have h := (LinearMap.toContinuousLinearMap f).hasFDerivAt.comp_hasDerivWithinAt s hd
  simpa [Function.comp_def] using h

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {m : ℕ} {h : SymmetricCubic V} {c : ℝ} {planes : PlaneDecomposition V (Fin m)}

/-- The tensor equation on the pencil at one time gives the coefficient equation. -/
theorem coeff_deriv_of_tensor (hm : 2 ≤ m) (hround : IsRound h c)
    (hclosed : IsClosedPlaneSystem h planes) (ε : ℝ) {u : ℝ → ℝ × ℝ} {S : Set ℝ} {s : ℝ}
    (hd : HasDerivWithinAt (fun r => coupling (planePencil h planes) (u r))
      (oneLoopBeta ε (coupling (planePencil h planes) (u s))) S s) :
    HasDerivWithinAt u (physicalCoefficientField c (pencilLambda V) ε (u s)) S s := by
  rw [Pencil.closedPencil_tangent h c planes hround hclosed ε] at hd
  exact hasDerivWithinAt_of_injective (coupling_injective hm hround hclosed) hd

/-- The coefficient equation gives the tensor equation on the pencil. -/
theorem tensor_deriv_of_coeff (hround : IsRound h c)
    (hclosed : IsClosedPlaneSystem h planes) (ε : ℝ) {u : ℝ → ℝ × ℝ} {S : Set ℝ} {s : ℝ}
    (hd : HasDerivWithinAt u (physicalCoefficientField c (pencilLambda V) ε (u s)) S s) :
    HasDerivWithinAt (fun r => coupling (planePencil h planes) (u r))
      (oneLoopBeta ε (coupling (planePencil h planes) (u s))) S s := by
  rw [Pencil.closedPencil_tangent h c planes hround hclosed ε]
  exact hasDerivWithinAt_map _ hd

end

end ThirteenPlanes.PencilFlow.Dynamics

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements Dynamics

/-- The one-loop pencil flow, the coefficient equations of the tensor flow on the pencil. -/
theorem coefficientEquations (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.FlowCoordinates V := by
  intro m hm h c planes hround hclosed ε _ u s hd
  dsimp only
  have hc := hround.positive
  have hlam := pencilLambda_pos hm planes
  have hK := flowScale_pos
  have hu : HasDerivAt u (physicalCoefficientField c (pencilLambda V) ε (u s)) s := by
    rw [← hasDerivWithinAt_univ] at hd ⊢
    exact coeff_deriv_of_tensor hm hround hclosed ε hd
  have hu1 : HasDerivAt (fun r => (u r).1)
      (physicalCoefficientField c (pencilLambda V) ε (u s)).1 s := by
    rw [← hasDerivWithinAt_univ] at hu ⊢; exact hu.fst
  have hu2 : HasDerivAt (fun r => (u r).2)
      (physicalCoefficientField c (pencilLambda V) ε (u s)).2 s := by
    rw [← hasDerivWithinAt_univ] at hu ⊢; exact hu.snd
  have hv1 : flowScale * (physicalCoefficientField c (pencilLambda V) ε (u s)).1 =
      (8 * Real.pi ^ 2 * ε - 3 * (2 * c * ((u s).1 ^ 2 + 3 * pencilLambda V * (u s).2 ^ 2)) / 2)
        * (u s).1 + 6 * c * pencilLambda V * (u s).2 ^ 3 := by
    simp only [physicalCoefficientField]; field_simp
  have hv2 : flowScale * (physicalCoefficientField c (pencilLambda V) ε (u s)).2 =
      (8 * Real.pi ^ 2 * ε - 3 * (2 * c * ((u s).1 ^ 2 + 3 * pencilLambda V * (u s).2 ^ 2)) / 2)
        * (u s).2 + 6 * c * (u s).2 ^ 2 * ((u s).1 - (u s).2 + pencilLambda V * (u s).2) := by
    simp only [physicalCoefficientField]; field_simp
  have hwedge : flowScale * ((u s).1 * (physicalCoefficientField c (pencilLambda V) ε (u s)).2 -
      (u s).2 * (physicalCoefficientField c (pencilLambda V) ε (u s)).1) =
      6 * c * (u s).2 ^ 2 * ((u s).1 - (u s).2) * ((u s).1 + pencilLambda V * (u s).2) := by
    linear_combination (u s).1 * hv2 - (u s).2 * hv1
  refine ⟨hu, hwedge, fun hg0 => ⟨?_, ?_⟩, fun hg0 hb0 => ⟨?_, ?_⟩⟩
  · have h := hu2.div hu1 hg0
    convert h using 1
    generalize (physicalCoefficientField c (pencilLambda V) ε (u s)).1 = A at hwedge ⊢
    generalize (physicalCoefficientField c (pencilLambda V) ε (u s)).2 = B at hwedge ⊢
    have hw' : (u s).1 * B - (u s).2 * A = 6 * c * (u s).2 ^ 2 * ((u s).1 - (u s).2) *
        ((u s).1 + pencilLambda V * (u s).2) / flowScale := by
      rw [eq_div_iff hK.ne']; linear_combination hwedge
    rw [show B * (u s).1 - (u s).2 * A = (u s).1 * B - (u s).2 * A by ring, hw']
    unfold ratioRate
    field_simp
    ring
  · convert hu1 using 1
    generalize (physicalCoefficientField c (pencilLambda V) ε (u s)).1 = A at hv1 ⊢
    have hv1' : A = ((8 * Real.pi ^ 2 * ε - 3 * (2 * c * ((u s).1 ^ 2 +
        3 * pencilLambda V * (u s).2 ^ 2)) / 2) * (u s).1 +
        6 * c * pencilLambda V * (u s).2 ^ 3) / flowScale := by
      rw [eq_div_iff hK.ne']; linear_combination hv1
    rw [hv1']
    unfold strengthRate
    field_simp
    ring
  · rw [hv1, hg0]; ring
  · intro h0
    have h1 : flowScale * (physicalCoefficientField c (pencilLambda V) ε (u s)).1 = 0 := by
      rw [h0, mul_zero]
    rw [hv1, hg0] at h1
    have h2 : 6 * c * pencilLambda V * (u s).2 ^ 3 = 0 := by linarith
    have hb3 : (u s).2 ^ 3 ≠ 0 := pow_ne_zero 3 hb0
    have : 0 < 6 * c * pencilLambda V := by positivity
    exact hb3 ((mul_eq_zero.mp h2).resolve_left this.ne')

end ThirteenPlanes.PencilFlow.Proofs
