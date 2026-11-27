module

public import ThirteenPlanes.Cartan.F4.FrameTransport
public import ThirteenPlanes.AlbertGrading.Grading.GradedPlanes
public import ThirteenPlanes.ClosedBlocks.Transport

@[expose] public section

set_option backward.privateInPublic true

/-! Normalize a scalar Casimir on the complement of one native graded plane. -/

open scoped BigOperators

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading RoundCubics

noncomputable section

private theorem operatorCasimir_apply_eq_zero_of_fixed
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (T : Submodule ℝ (SkewOperator V)) (x : V) (hx : x ∈ fixedSpace T) :
    operatorCasimir T x = 0 := by
  let b := stdOrthonormalBasis ℝ T
  rw [operatorCasimir_eq_sum T b, LinearMap.neg_apply, LinearMap.sum_apply]
  have he (i : Fin (Module.finrank ℝ T)) : ((b i).val.val * (b i).val.val) x = 0 := by
    change (b i).val.val ((b i).val.val x) = 0
    rw [(mem_fixedSpace T x).mp hx (b i), map_zero]
  simp only [he, Finset.sum_const_zero, neg_zero]

private theorem trace_projection_eq_finrank
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (U : Submodule ℝ V) :
    LinearMap.trace ℝ V (projection U) = Module.finrank ℝ U := by
  have h : LinearMap.IsProj U (projection U) :=
    ⟨U.starProjection_apply_mem, fun x hx => U.starProjection_mem_subspace_eq_self ⟨x, hx⟩⟩
  exact h.trace

/-- If the other graded planes all have the same Casimir value, the trace determines the
value (1/6) on their 24-dimensional sum. -/
theorem nativeAlbertFrameType_of_scalar_pointPlanes {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)
    (p : SignedPlaneIndex) (T : Submodule ℝ (SkewOperator albertJordan.traceFree))
    (hcomm : IsCommutativeSpace T) (hdim : Module.finrank ℝ T = 4)
    (hfixed : fixedSpace T = (pointPlane ρ p).map albertTraceEquiv.symm.toLinearMap)
    (a : ℝ)
    (hscalar : ∀ q ≠ p, ∀ x ∈ (pointPlane ρ q).map albertTraceEquiv.symm.toLinearMap,
      operatorCasimir T x = a • x) :
    IsFrameType T 4 (1 / 6) := by
  let Q (q : SignedPlaneIndex) := (pointPlane ρ q).map albertTraceEquiv.symm.toLinearMap
  have hfill : (⨆ q, Q q) = ⊤ := by
    change (⨆ q, (pointPlane ρ q).map albertTraceEquiv.symm.toLinearMap) = ⊤
    rw [← Submodule.map_iSup, pointPlanes_fill hρ, Submodule.map_top,
      LinearMap.range_eq_top.mpr albertTraceEquiv.symm.surjective]
  have hfixedDim : Module.finrank ℝ (fixedSpace T) = 2 := by
    rw [hfixed, ← (albertTraceEquiv.symm.toLinearEquiv.submoduleMap (pointPlane ρ p)).finrank_eq,
      pointPlane_finrank hρ]
  let C := operatorCasimir T - a • (LinearMap.id - projection (fixedSpace T))
  have hk : (⨆ q, Q q) ≤ LinearMap.ker C := by
    apply iSup_le
    intro q x hx
    apply LinearMap.mem_ker.mpr
    change operatorCasimir T x - a • (x - (fixedSpace T).starProjection x) = 0
    by_cases hqp : q = p
    · subst q
      have hmem : x ∈ fixedSpace T := hfixed.symm ▸ hx
      rw [operatorCasimir_apply_eq_zero_of_fixed T x hmem,
        Submodule.starProjection_eq_self_iff.mpr hmem, sub_self, smul_zero, sub_zero]
    · have horth : (Q q).IsOrtho (fixedSpace T) := by
        rw [hfixed]
        exact isOrtho_map_isometry albertTraceEquiv.symm (pointPlane_orthogonal hρ hqp)
      have hproj : (fixedSpace T).starProjection x = 0 :=
        (fixedSpace T).eq_starProjection_of_mem_orthogonal (u := x) (v := 0)
          (Submodule.zero_mem _) (by simpa only [sub_zero] using horth.le hx)
      rw [hscalar q hqp x hx, hproj, sub_zero, sub_self]
  have hC : C = 0 := LinearMap.ker_eq_top.mp
    (top_le_iff.mp (hfill ▸ hk))
  have heq : operatorCasimir T = a • (LinearMap.id - projection (fixedSpace T)) :=
    sub_eq_zero.mp hC
  have hdimV : Module.finrank ℝ albertJordan.traceFree = 26 :=
    albertTraceEquiv.toLinearEquiv.finrank_eq.trans nativeTraceless_finrank
  have htrace := trace_operatorCasimir T
  rw [heq, map_smul, map_sub, LinearMap.trace_id, trace_projection_eq_finrank,
    hdimV, hfixedDim, hdim] at htrace
  have ha : a = (1 / 6 : ℝ) := by
    change a * ((26 : ℝ) - 2) = 4 at htrace
    linarith
  exact ⟨hcomm, hdim, hfixedDim, ha ▸ heq⟩

end

end ThirteenPlanes.Cartan
