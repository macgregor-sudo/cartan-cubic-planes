module

public import ThirteenPlanes.PencilFlow.Hessian.PointSpectrum
public import ThirteenPlanes.CubicRotationChart
public import ThirteenPlanes.ChargeFixedAttractionChart

@[expose] public section

/-! Forward existence, uniqueness and convergence to a point in the round orbit for
the rescaled flow starting near that orbit (Proposition 9-hessian(c)).

The Hessian has eigenvalues at least one on the normal space to the rotation orbit.
The contracting chart `ChargeFixed.smooth_chart_has_attracting_neighborhood` gives local
convergence at a floor cubic. Orthogonal pullback transports the chart and Mathlib's
Lipschitz ODE theorem gives uniqueness. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology ContDiff

namespace ThirteenPlanes.PencilFlow.HessianBridge

noncomputable section

open SymmetricCubic Statements

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Off the rotation tangent the Hessian form dominates the squared norm. -/
theorem floor_normal_hessian (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfloor : aFunction C = floorValue (Module.finrank ℝ V)) (y : rotationNormal C) :
    ‖y‖ ^ 2 ≤ aHessian C y y := by
  obtain ⟨⟨r, t, w⟩, hsum, _⟩ := existsUnique_decomposition hn hfloor (y : SymmetricCubic V)
  change (r : SymmetricCubic V) + t + w = y at hsum
  have hry : ⟪(r : SymmetricCubic V), (y : SymmetricCubic V)⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal r.property y.property
  have hrt := rotation_orth_trace hn hfloor r.property t.property
  have hrw := rotation_orth_complement r.property w.property
  rw [← hsum, inner_add_right, inner_add_right, inner_eq_tensorPairing, inner_eq_tensorPairing,
    inner_eq_tensorPairing, hrt, hrw, add_zero, add_zero] at hry
  have hr0 : (r : SymmetricCubic V) = 0 := eq_zero_of_tensorPairing_self _ hry
  have hy : (t : SymmetricCubic V) + (w : SymmetricCubic V) = y := by
    simpa only [hr0, zero_add] using hsum
  have htw := trace_orth_complement t.property w.property
  have hnorm : ‖y‖ ^ 2 = t.val.tensorPairing t.val + w.val.tensorPairing w.val := by
    calc
      ‖y‖ ^ 2 = ⟪(y : SymmetricCubic V), (y : SymmetricCubic V)⟫ :=
        (real_inner_self_eq_norm_sq y).symm
      _ = _ := by rw [← hy, inner_add_right, inner_add_left, inner_add_left, inner_eq_tensorPairing,
                    inner_eq_tensorPairing, inner_eq_tensorPairing, inner_eq_tensorPairing,
                    htw, tensorPairing_comm w.val t.val, htw, zero_add, add_zero]
  have hh := aHessian_spectral_self hn hfloor r.property t.property w.property
  rw [hsum] at hh
  rw [hnorm, hh]
  have hl := one_lt_traceEigenvalue (Module.finrank ℝ V)
  nlinarith [tensorPairing_self_nonneg t.val]

theorem pullback_smul_cubic (a : ℝ) (D : SymmetricCubic V) (Q : V ≃ₗᵢ[ℝ] V) :
    (a • D).pullback Q.toLinearMap = a • D.pullback Q.toLinearMap := by
  apply SymmetricCubic.ext; intro x y z; simp

theorem rescaledField_pullback (Q : V ≃ₗᵢ[ℝ] V) (D : SymmetricCubic V) :
    rescaledField (D.pullback Q.toLinearMap) = (rescaledField D).pullback Q.toLinearMap := by
  rw [rescaledField_eq, rescaledField_eq, oneLoopBeta_pullback_isometry, pullback_smul_cubic]

/-- Local attraction near the base point of the orbit. -/
theorem floor_attracting_neighborhood (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    ∃ U : Set (SymmetricCubic V), IsOpen U ∧ C ∈ U ∧
      ∀ X ∈ U, ∃ u : ℝ → SymmetricCubic V, u 0 = X ∧
        (∀ t ≥ 0, HasDerivWithinAt u (rescaledField (u t)) (Ici 0) t) ∧
        ∃ Q : V ≃ₗᵢ[ℝ] V, Tendsto u atTop (𝓝 (C.pullback Q.toLinearMap)) := by
  let B := rescaledField (V := V)
  let φ := rotationChart C
  have hC0 := rescaledField_floor hn hfl
  have hz (x : rotationSpace C) : B (φ (x, 0)) = 0 := by
    obtain ⟨Q, hQ⟩ := rotationChart_slice C x
    change rescaledField (rotationChart C (x, 0)) = 0
    rw [hQ, rescaledField_pullback, hC0]
    apply SymmetricCubic.ext; intro x y z; simp
  obtain ⟨U, hU, h0, hUFlow⟩ := ChargeFixed.smooth_chart_has_attracting_neighborhood B φ
    (rotationChartLinearEquiv C) (rotationChart_contDiff C 2).contDiffAt
    (rotationChart_hasFDerivAt C) (rescaledField_contDiff 1).contDiffAt
    (Eventually.of_forall hz) (half_pos one_pos) (by
      intro y
      let d := rotationChartLinearEquiv C
      rw [show φ 0 = C from rotationChart_zero C]
      have hd₀ : d (0, y) = (y : SymmetricCubic V) := by
        change rotationChartLinearEquiv C (0, y) = _
        rw [rotationChartLinearEquiv_apply]
        exact zero_add _
      rw [hd₀]
      let w := fderiv ℝ B C (y : SymmetricCubic V)
      let p := d.symm w
      have hsum : (p.1 : SymmetricCubic V) + (p.2 : SymmetricCubic V) = w :=
        (rotationChartLinearEquiv_apply C p).symm.trans (d.apply_symm_apply w)
      have horth : ⟪(y : SymmetricCubic V), (p.1 : SymmetricCubic V)⟫ = 0 :=
        Submodule.inner_left_of_mem_orthogonal p.1.property y.property
      have hi : ⟪(y : SymmetricCubic V), w⟫ = ⟪y, p.2⟫ := by
        rw [← hsum, inner_add_right, horth, zero_add]
        rfl
      change ⟪y, p.2⟫ ≤ _
      rw [← hi]
      change ⟪(y : SymmetricCubic V), fderiv ℝ rescaledField C (y : SymmetricCubic V)⟫ ≤ _
      rw [inner_fderiv_rescaledField]
      have := floor_normal_hessian hn hfl y
      linarith)
  refine ⟨U, hU, ?_, ?_⟩
  · simpa only [φ, rotationChart_zero] using h0
  · intro X hX
    obtain ⟨u, hu, hdu, x, _, hlim⟩ := hUFlow X hX
    obtain ⟨Q, hQ⟩ := rotationChart_slice C x
    exact ⟨u, hu, hdu, Q, hQ ▸ hlim⟩

/-- Local attraction near the whole orbit. -/
theorem floor_orbit_attracting_neighborhood (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    ∃ U : Set (SymmetricCubic V), IsOpen U ∧
      (∀ Q : V ≃ₗᵢ[ℝ] V, C.pullback Q.toLinearMap ∈ U) ∧
      ∀ X ∈ U, ∃ u : ℝ → SymmetricCubic V, u 0 = X ∧
        (∀ t ≥ 0, HasDerivWithinAt u (rescaledField (u t)) (Ici 0) t) ∧
        ∃ Q : V ≃ₗᵢ[ℝ] V, Tendsto u atTop (𝓝 (C.pullback Q.toLinearMap)) := by
  obtain ⟨U, hU, hBase, hFlow⟩ := floor_attracting_neighborhood hn hfl
  let W := ⋃ Q : V ≃ₗᵢ[ℝ] V, (orthogonalPullback Q) '' U
  refine ⟨W, isOpen_iUnion (fun Q => (orthogonalPullback Q).isOpenMap _ hU), ?_, ?_⟩
  · intro Q
    exact mem_iUnion.mpr ⟨Q, C, hBase, rfl⟩
  · intro X hX
    obtain ⟨Q, D, hD, rfl⟩ := mem_iUnion.mp hX
    obtain ⟨u, hu, hdu, P, hP⟩ := hFlow D hD
    let A := (orthogonalPullback Q).toContinuousLinearMap
    refine ⟨A ∘ u, congrArg A hu, ?_, Q.trans P, ?_⟩
    · intro t ht
      have h := A.hasFDerivAt.comp_hasDerivWithinAt t (hdu t ht)
      change HasDerivWithinAt (A ∘ u) (rescaledField (A (u t))) (Ici 0) t
      rw [show A (u t) = (u t).pullback Q.toLinearMap from rfl, rescaledField_pullback]
      exact h
    · have h := (A.continuous.tendsto _).comp hP
      have he : A (C.pullback P.toLinearMap) = C.pullback (Q.trans P).toLinearMap := by
        apply SymmetricCubic.ext
        intro x y z
        change ((C.pullback P.toLinearMap).pullback Q.toLinearMap).apply x y z = _
        simp only [pullback_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
          LinearIsometryEquiv.trans_apply]
      rwa [he] at h

/-- Uniqueness of rescaled-flow solutions on a compact forward interval. -/
theorem rescaled_unique_Icc {f g : ℝ → SymmetricCubic V} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (rescaledField (f t)) (Icc 0 T) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivWithinAt g (rescaledField (g t)) (Icc 0 T) t)
    (h0 : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  have hfc : ContinuousOn f (Icc 0 T) := fun t ht => (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 T) := fun t ht => (hg t ht).continuousWithinAt
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  set R := max Mf Mg
  obtain ⟨K, hK⟩ := ((rescaledField_contDiff (V := V) 1).contDiffOn
    (s := Metric.closedBall 0 R)).exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 R)
    (isCompact_closedBall 0 R)
  have hnhds : ∀ t ∈ Ico (0 : ℝ) T, Icc 0 T ∈ 𝓝[Ici t] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => rescaledField)
    (s := fun _ => Metric.closedBall 0 R) (fun _ _ => hK) hfc
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hnhds t ht))
    (fun t ht => mem_closedBall_zero_iff.mpr ((hMf t (Ico_subset_Icc_self ht)).trans
      (le_max_left _ _)))
    hgc (fun t ht => (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hnhds t ht))
    (fun t ht => mem_closedBall_zero_iff.mpr ((hMg t (Ico_subset_Icc_self ht)).trans
      (le_max_right _ _)))
    h0

end

end ThirteenPlanes.PencilFlow.HessianBridge

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements HessianBridge

/-- Proposition 9-hessian (c). -/
theorem roundOrbitLocalConvergence (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Statements.HessianC V := by
  intro h c hT hR
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hfl := unitRound_floor hT hR
  obtain ⟨U, hU, hOrbit, hFlow⟩ := floor_orbit_attracting_neighborhood hn hfl
  refine ⟨U, hU, hOrbit, fun X hX => ?_⟩
  obtain ⟨u, hu0, hdu, Q, hlim⟩ := hFlow X hX
  have hseg : ∀ (T : ℝ) (segment : ℝ → SymmetricCubic V), segment 0 = X →
      IsIntegralCurveOn segment (fun _ => rescaledField) (Icc 0 T) → EqOn u segment (Icc 0 T) :=
    fun T segment hs0 hs => rescaled_unique_Icc
      (fun t ht => (hdu t ht.1).mono Icc_subset_Ici_self) hs (hu0.trans hs0.symm)
  refine ⟨⟨u, hu0, fun t ht => hdu t ht, fun T segment _ hs0 hs => hseg T segment hs0 hs⟩, ?_⟩
  intro γ hγ0 hγ
  refine ⟨Q, hlim.congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hseg t γ hγ0 (fun s hs => (hγ s hs.1).mono Icc_subset_Ici_self) ⟨ht, le_rfl⟩

end ThirteenPlanes.PencilFlow.Proofs
