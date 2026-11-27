module

public import ThirteenPlanes.Peirce.FrameFormula
public import ThirteenPlanes.Peirce.SlotClosedPlaneIdentification
public import ThirteenPlanes.Shares.NativeTraceFrames

@[expose] public section

set_option backward.privateInPublic true

/-! The printed frame formula on the actual Albert trace carrier. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {h : SymmetricCubic V}

private def nativeFrameEmbedding (I : V →ₗᵢ[ℝ] NativeTraceless) : V →ₗᵢ[ℝ] Glennie.Albert :=
  nativeTraceInclusion.comp I

omit [FiniteDimensional ℝ V] in
private theorem nativeFrameEmbedding_trace_zero (I : V →ₗᵢ[ℝ] NativeTraceless) (x : V) :
    ⟪(1 : Glennie.Albert), nativeFrameEmbedding I x⟫ = 0 := by
  change Glennie.inner 1 (I x : NativeTraceless) = 0
  rw [nativeInner_one_left, nativeTraceless_trace]

omit [FiniteDimensional ℝ V] in
set_option maxHeartbeats 1200000 in
private theorem nativeFrameEmbedding_product_of_intertwines (I : V →ₗᵢ[ℝ] NativeTraceless)
    (intertwines : ∀ x y, I (h.L x y) = Real.sqrt 6 • nativeCenteredJordan (I x) (I y))
    (x y : V) :
    nativeFullCubic.L (nativeFrameEmbedding I x) (nativeFrameEmbedding I y) =
      (Real.sqrt 6)⁻¹ • nativeFrameEmbedding I (h.L x y) + (⟪x, y⟫ / 3) • (1 : Glennie.Albert) := by
  change Glennie.jordan (I x : NativeTraceless) (I y : NativeTraceless) =
    (Real.sqrt 6)⁻¹ • (I (h.L x y) : NativeTraceless) + (⟪x, y⟫ / 3) • (1 : Glennie.Albert)
  rw [intertwines, Submodule.coe_smul, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne', one_smul,
    nativeCenteredJordan_apply, nativeCenter_coe, Glennie.traceless]
  have hi := LinearIsometry.inner_map_map (𝕜 := ℝ) I x y
  change Glennie.trace (Glennie.jordan (I x : NativeTraceless) (I y : NativeTraceless)) = ⟪x, y⟫ at hi
  rw [hi]
  abel

/-- The native full product splits into the transported centered product and its scalar trace. -/
theorem nativeFrameEmbedding_product (I : V ≃ₗᵢ[ℝ] NativeTraceless)
    (hI : h = nativeCartanCubic.pullback I.toLinearMap) (x y : V) :
    nativeFullCubic.L (nativeFrameEmbedding I.toLinearIsometry x) (nativeFrameEmbedding I.toLinearIsometry y) =
      (Real.sqrt 6)⁻¹ • nativeFrameEmbedding I.toLinearIsometry (h.L x y) +
        (⟪x, y⟫ / 3) • (1 : Glennie.Albert) :=
  nativeFrameEmbedding_product_of_intertwines I.toLinearIsometry (pullback_intertwines_product I hI) x y

omit [FiniteDimensional ℝ V] in
set_option maxHeartbeats 1200000 in
/-- Lemma 2b-frames, on the actual Albert carrier. -/
theorem nativeFrame_of_three_unit_idempotents_of_intertwines (I : V →ₗᵢ[ℝ] NativeTraceless)
    (intertwines : ∀ x y, I (h.L x y) = Real.sqrt 6 • nativeCenteredJordan (I x) (I y))
    (a : Fin 3 → V) (ha : ∀ i, IsUnitIdempotent h (a i)) (hs : ∑ i, a i = 0) :
    Glennie.Frame (fun i => (1 / 3 : ℝ) • ((1 : Glennie.Albert) + Real.sqrt 6 • (I (a i) : NativeTraceless))) := by
  have hrank : ⟪(1 : Glennie.Albert), (1 : Glennie.Albert)⟫ = 3 := by
    change Glennie.inner 1 1 = 3
    rw [nativeInner_one_left, Glennie.trace_unit]
  have H := frame_of_three_unit_idempotents h nativeFullCubic 1 (nativeFrameEmbedding I)
    Glennie.jordan_unit_left hrank (nativeFrameEmbedding_trace_zero I) (nativeFrameEmbedding_product_of_intertwines I intertwines) a ha hs
  refine ⟨?_, H.idempotent, H.orthogonal, ?_⟩
  · intro i
    have ht := H.trace_one i
    change Glennie.inner 1 _ = 1 at ht
    rw [nativeInner_one_left] at ht
    exact ht
  · change framePoint (nativeFrameEmbedding I) 1 (a 0) + framePoint (nativeFrameEmbedding I) 1 (a 1) +
      framePoint (nativeFrameEmbedding I) 1 (a 2) = 1
    simpa only [Fin.sum_univ_three] using H.sum_unit

/-- The frame formula for a round cubic identified with the native Cartan cubic. -/
theorem nativeFrame_of_three_unit_idempotents (I : V ≃ₗᵢ[ℝ] NativeTraceless)
    (hI : h = nativeCartanCubic.pullback I.toLinearMap)
    (a : Fin 3 → V) (ha : ∀ i, IsUnitIdempotent h (a i)) (hs : ∑ i, a i = 0) :
    Glennie.Frame (fun i => (1 / 3 : ℝ) • ((1 : Glennie.Albert) + Real.sqrt 6 • (I (a i) : NativeTraceless))) :=
  nativeFrame_of_three_unit_idempotents_of_intertwines I.toLinearIsometry
    (pullback_intertwines_product I hI) a ha hs

omit [FiniteDimensional ℝ V] in
/-- Every cross-overlap between frame points from orthogonal source planes is one third. -/
theorem nativeFrame_formula_unbiased (I : V →ₗᵢ[ℝ] NativeTraceless) {x y : V} (ho : ⟪x, y⟫ = 0) :
    Glennie.inner ((1 / 3 : ℝ) • ((1 : Glennie.Albert) + Real.sqrt 6 • (I x : NativeTraceless)))
      ((1 / 3 : ℝ) • ((1 : Glennie.Albert) + Real.sqrt 6 • (I y : NativeTraceless))) = 1 / 3 := by
  have hrank : ⟪(1 : Glennie.Albert), (1 : Glennie.Albert)⟫ = 3 := by
    change Glennie.inner 1 1 = 3
    rw [nativeInner_one_left, Glennie.trace_unit]
  exact framePoint_inner_of_orthogonal (nativeFrameEmbedding I) 1 hrank (nativeFrameEmbedding_trace_zero I) ho

end

end ThirteenPlanes.Peirce
