/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRow.AllDecompositions
public import ThirteenPlanes.Cartan.SecondRowLieRealization

@[expose] public section

set_option backward.privateInPublic true

/-! Orthogonal decompositions in the compact Lie algebra of second-row operators. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {ι : Type*} [DecidableEq ι]

private theorem internal_map_equiv {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (e : V ≃ₗ[ℝ] W) (P : ι → Submodule ℝ V)
    (h : DirectSum.IsInternal P) : DirectSum.IsInternal (fun i => (P i).map e.toLinearMap) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (R := ℝ) (M := W)
  · exact e.toLinearMap.iSupIndep_map e.injective h.submodule_iSupIndep
  · rw [← Submodule.map_iSup, h.submodule_iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

private theorem internal_equiv_iff {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (e : V ≃ₗ[ℝ] W) (P : ι → Submodule ℝ V)
    (Q : ι → Submodule ℝ W) (eq : ∀ i, (P i).map e.toLinearMap = Q i) :
    DirectSum.IsInternal P ↔ DirectSum.IsInternal Q := by
  constructor
  · intro h
    exact (funext eq) ▸ internal_map_equiv e P h
  · intro h
    have back (i) : (Q i).map e.symm.toLinearMap = P i := by
      rw [← eq i, ← Submodule.comap_equiv_eq_map_symm, Submodule.comap_map_eq_of_injective e.injective]
    exact (funext back) ▸ internal_map_equiv e.symm Q h

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
  {M : TraceJordanData J} {K : Submodule ℝ (SkewOperator J)} (H : SecondRowCompactRealization M K)

/-- The complex trace pairing on this real Lie algebra has real values. -/
theorem secondRow_pairing_vanishes_iff_real (X Y : secondRowSpace M K) :
    complexTraceForm X.val Y.val = 0 ↔ (complexTraceForm X.val Y.val).re = 0 := by
  obtain ⟨p, rfl⟩ := (secondRowCoordinates M K).surjective X
  obtain ⟨q, rfl⟩ := (secondRowCoordinates M K).surjective Y
  change complexTraceForm (secondRowEmbed M K p) (secondRowEmbed M K q) = 0 ↔
    (complexTraceForm (secondRowEmbed M K p) (secondRowEmbed M K q)).re = 0
  rw [secondRow_traceForm, Complex.ofReal_eq_zero, Complex.ofReal_re]

/-- A positive scalar relating the two real forms gives the same orthogonality for
the literal operator trace and the Killing form on the quoted compact Lie algebra. -/
theorem secondRow_trace_killing_orthogonal
    (proportional : ∃ a : ℝ, 0 < a ∧ ∀ X Y : H.operators,
      (complexTraceForm X.val Y.val).re = a * (-killingForm ℝ H.operators X Y))
    (X Y : secondRowSpace M K) :
    complexTraceForm X.val Y.val = 0 ↔ killingForm ℝ H.operators (H.coordinates X) (H.coordinates Y) = 0 := by
  obtain ⟨a, hp, eq⟩ := proportional
  rw [secondRow_pairing_vanishes_iff_real]
  change (complexTraceForm (H.coordinates X).val (H.coordinates Y).val).re = 0 ↔ _
  rw [eq, mul_eq_zero]
  simp [hp.ne']

set_option maxHeartbeats 1000000 in
/-- A family of Lie subalgebras and a family of operator spaces with the same actual
operators satisfy exactly the same Cartan, orthogonality, and stability conditions. -/
theorem secondRowLieCartanOD_iff (P : ι → Submodule ℝ (secondRowSpace M K))
    (B : ι → LieSubalgebra ℝ H.operators) (same : ∀ i, (P i).map H.coordinates.toLinearMap = (B i).toSubmodule)
    (metric : ∀ X Y : secondRowSpace M K, complexTraceForm X.val Y.val = 0 ↔
      killingForm ℝ H.operators (H.coordinates X) (H.coordinates Y) = 0) :
    StableSecondRowCartanOD M K P ↔ IsKillingCartanOD B ∧
      ∀ i, (B i).toSubmodule.map H.theta.toLinearMap = (B i).toSubmodule := by
  let Q i := (B i).toSubmodule
  have cartan (i) : MaximalCommutativeSubspace (SecondRowOperatorCommutative M K) (P i) ↔
      (B i).IsCartanSubalgebra := by
    rw [maximalSecondRowCartan_iff_represented, ← H.operatorCartan_iff,
      ← same i, Submodule.comap_map_eq_of_injective H.coordinates.injective]
  have conjugation : H.coordinates.toLinearMap.comp (secondRowTheta M K).toLinearMap =
      H.theta.toLinearMap.comp H.coordinates.toLinearMap :=
    LinearMap.ext fun X => (H.theta_coordinates X).symm
  have stable (i) : (P i).map (secondRowTheta M K).toLinearMap = P i ↔
      (Q i).map H.theta.toLinearMap = Q i := by
    rw [← (Submodule.map_injective_of_injective H.coordinates.injective).eq_iff]
    rw [← Submodule.map_comp, conjugation, Submodule.map_comp, same i]
  have mem (i) (X : secondRowSpace M K) : H.coordinates X ∈ B i ↔ X ∈ P i := by
    change X ∈ (Q i).comap H.coordinates.toLinearMap ↔ X ∈ P i
    rw [show Q i = (P i).map H.coordinates.toLinearMap from (same i).symm,
      Submodule.comap_map_eq_of_injective H.coordinates.injective]
  have inter := internal_equiv_iff (V := ↥(secondRowSpace M K)) (W := ↥H.operators)
    (ι := ι) H.coordinates P Q same
  have ds := DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (R := ℝ)
    (M := ↥(secondRowSpace M K)) P
  constructor
  · intro h
    refine ⟨⟨fun i => (cartan i).mp (h.cartan i), ?_, inter.mp (ds.mpr ⟨h.independent, h.spans⟩)⟩,
      fun i => (stable i).mp (h.stable i)⟩
    intro i j hij x hx y hy
    obtain ⟨X, rfl⟩ := H.coordinates.surjective x
    obtain ⟨Y, rfl⟩ := H.coordinates.surjective y
    exact (metric X Y).mp (h.orthogonal i j hij X ((mem i X).mp hx) Y ((mem j Y).mp hy))
  · rintro ⟨h, hs⟩
    have hp := ds.mp (inter.mpr h.2.2)
    refine ⟨fun i => (cartan i).mpr (h.1 i), fun i => (stable i).mpr (hs i), hp.1, hp.2, ?_⟩
    intro i j hij X hX Y hY
    exact (metric X Y).mpr (h.2.1 hij _ ((mem i X).mpr hX) _ ((mem j Y).mpr hY))

end
end ThirteenPlanes.Cartan
