module

public import ThirteenPlanes.Quaternionic.NativeTraceModel
public import ThirteenPlanes.Shares.TraceFrames

@[expose] public section

set_option backward.privateInPublic true

/-! The geometric half-trace share of arbitrary native quaternionic frame triples. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace QuaternionicMUB

open ThirteenPlanes ThirteenPlanes.RoundCubics

noncomputable section

/-- The actual frame plane of centered rank-one quaternionic projections. -/
def Frame.centeredPlane (F : Frame) : Submodule ℝ TracelessHilbert :=
  Submodule.span ℝ (Set.range F.centeredHilbert)

theorem Frame.centeredHilbert_mem_plane (F : Frame) (a : Outcome) :
    F.centeredHilbert a ∈ F.centeredPlane :=
  Submodule.subset_span ⟨a, rfl⟩

@[simp] theorem traceMat_centeredHilbert (F : Frame) (a : Outcome) :
    traceMat (F.centeredHilbert a) = F.centeredPointMatrix a :=
  congrArg Subtype.val (tracelessHilbertEquiv.apply_symm_apply (F.centeredPoint a))

theorem Frame.centeredPlane_dimension (F : Frame) :
    Module.finrank ℝ F.centeredPlane = 2 := by
  let B := Submodule.span ℝ (Set.range F.planeOrtho)
  have hplane : F.centeredPlane = B := by
    apply le_antisymm
    · have hu (i : Fin 2) : F.planeOrtho i ∈ B := Submodule.subset_span ⟨i, rfl⟩
      have h₀ : F.centeredHilbert 0 ∈ B := by
        have h := B.smul_mem ((Real.sqrt (3 / 2 : ℝ))⁻¹) (hu 0)
        rw [F.planeOrtho_zero, smul_smul,
          inv_mul_cancel₀ (Real.sqrt_pos.2 (by norm_num : 0 < (3 / 2 : ℝ))).ne',
          one_smul] at h
        exact h
      have h₁ : F.centeredHilbert 1 ∈ B := by
        have h := B.smul_mem ((Real.sqrt 2)⁻¹) (hu 1)
        rw [F.planeOrtho_one, smul_smul,
          inv_mul_cancel₀ (Real.sqrt_pos.2 (by norm_num : 0 < (2 : ℝ))).ne',
          one_smul] at h
        have h' := B.sub_mem h (B.smul_mem (1 / 2 : ℝ) h₀)
        rwa [add_sub_cancel_right] at h'
      have h₂ : F.centeredHilbert 2 ∈ B := by
        have hs := F.sum_centeredHilbert
        rw [Fin.sum_univ_three] at hs
        have he : F.centeredHilbert 2 = -(F.centeredHilbert 0 + F.centeredHilbert 1) := by
          calc
            _ = (F.centeredHilbert 0 + F.centeredHilbert 1 + F.centeredHilbert 2) -
                (F.centeredHilbert 0 + F.centeredHilbert 1) := by abel
            _ = _ := by rw [hs, zero_sub]
        rw [he]
        exact B.neg_mem (B.add_mem h₀ h₁)
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      fin_cases a <;> assumption
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · change F.planeOrtho 0 ∈ F.centeredPlane
        rw [F.planeOrtho_zero]
        exact F.centeredPlane.smul_mem _ (F.centeredHilbert_mem_plane 0)
      · change F.planeOrtho 1 ∈ F.centeredPlane
        rw [F.planeOrtho_one]
        exact F.centeredPlane.smul_mem _ (F.centeredPlane.add_mem
          (F.centeredHilbert_mem_plane 1)
          (F.centeredPlane.smul_mem _ (F.centeredHilbert_mem_plane 0)))
  rw [hplane]
  exact (finrank_span_eq_card F.planeOrtho_orthonormal.linearIndependent).trans (Fintype.card_fin 2)

theorem Frame.centeredPlane_orthogonal {F G : Frame} (h : F.MutuallyUnbiased G) :
    F.centeredPlane.IsOrtho G.centeredPlane := by
  rw [Submodule.isOrtho_iff_le]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  have hg : G.centeredPlane ≤ (ℝ ∙ F.centeredHilbert a)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    have he : ⟪F.centeredHilbert a, G.centeredHilbert b⟫ = 0 := by
      rw [F.centeredHilbert_inner]
      exact (mutuallyUnbiased_iff_centered_orthogonal F G).mp h a b
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr he
  exact (Submodule.mem_orthogonal' G.centeredPlane _).mpr fun y hy =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hg hy)

private theorem jordan_centered_points (F : Frame) (a b : Outcome) :
    jordan (F.centeredPointMatrix a) (F.centeredPointMatrix b) =
      jordan (F.point a) (F.point b) -
        (1 / 3 : ℝ) • (F.point a + F.point b) + (1 / 9 : ℝ) • (1 : QMat) := by
  simp only [Frame.centeredPointMatrix, jordan, sub_mul, mul_sub, mul_smul_comm,
    smul_mul_assoc, one_mul, mul_one, smul_sub, smul_add, smul_smul]
  module

private theorem centeredProduct_points (F : Frame) (a b : Outcome) :
    quaternionTraceCubic.L (F.centeredHilbert a) (F.centeredHilbert b) =
      (if a = b then F.centeredHilbert a else 0) -
        (1 / 3 : ℝ) • (F.centeredHilbert a + F.centeredHilbert b) := by
  apply traceMat_injective
  rw [quaternionTraceCubic_L_matrix, traceMat_centeredHilbert, traceMat_centeredHilbert,
    jordan_centered_points]
  by_cases hab : a = b
  · subst b
    simp only [map_sub, map_smul, map_add, traceMat_centeredHilbert,
      F.idempotent, Frame.centeredPointMatrix, centerMatrix, rtrace_add, rtrace_sub,
      rtrace_smul, F.trace_one, rtrace_one]
    simp only [ite_true, traceMat_centeredHilbert, Frame.centeredPointMatrix]
    module
  · simp only [ite_eq_right hab, map_sub, map_smul, map_add, map_zero, traceMat_centeredHilbert,
      F.orthogonal a b hab, Frame.centeredPointMatrix, centerMatrix, rtrace_add, rtrace_sub,
      rtrace_smul, F.trace_one, rtrace_one, rtrace_zero]
    module

theorem Frame.centeredPlane_closed (F : Frame) :
    IsClosedPiece quaternionTraceCubic F.centeredPlane := by
  classical
  let S := F.centeredPlane
  have hpoint (a b : Outcome) :
      quaternionTraceCubic.L (F.centeredHilbert a) (F.centeredHilbert b) ∈ S := by
    rw [centeredProduct_points]
    refine S.sub_mem ?_ (S.smul_mem _ (S.add_mem
      (F.centeredHilbert_mem_plane a) (F.centeredHilbert_mem_plane b)))
    split <;> first | exact F.centeredHilbert_mem_plane a | exact S.zero_mem
  have hx (a : Outcome) :
      S ≤ S.comap (quaternionTraceCubic.L (F.centeredHilbert a)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    exact hpoint a b
  intro u v hu hv
  have hy : S ≤ S.comap (quaternionTraceCubic.L v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    change quaternionTraceCubic.L v (F.centeredHilbert a) ∈ S
    rw [quaternionTraceCubic.L_comm]
    exact hx a hv
  rw [quaternionTraceCubic.L_comm]
  exact hy hu

/-- The actual rank-three frame in the universal trace interface. -/
def nativeCenteredTraceFrame (F : Frame) :
    CenteredTraceFrame traceInclusion fullUnit F.centeredPlane where
  point a := fullOfMatrix (F.point a) (F.hermitian a)
  orthonormal := by
    apply orthonormal_iff_ite.mpr
    intro a b
    rw [hermitianHilbert_inner]
    change traceForm (fullMat (fullOfMatrix (F.point a) (F.hermitian a)))
      (fullMat (fullOfMatrix (F.point b) (F.hermitian b))) = _
    rw [fullMat_ofMatrix, fullMat_ofMatrix, F.traceForm_points]
  point_sum := by
    apply fullMat_injective
    rw [map_sum, fullMat_fullUnit]
    simp only [fullMat_ofMatrix, F.sum_points]
  centered a := ⟨F.centeredHilbert a, F.centeredHilbert_mem_plane a⟩
  centered_eq := by
    intro a
    apply fullMat_injective
    rw [fullMat_traceInclusion, traceMat_centeredHilbert, map_sub, map_smul,
      fullMat_ofMatrix, fullMat_fullUnit]
    rfl
  span_centered := (Submodule.span_range_subtype_eq_top_iff F.centeredPlane
    F.centeredHilbert_mem_plane).mpr rfl

/-- The geometric half-trace share is literally the native 27-entry triple trace. -/
theorem frameShare_eq_frameS (F G H : Frame) (hFG : F.MutuallyUnbiased G)
    (hFH : F.MutuallyUnbiased H) (hGH : G.MutuallyUnbiased H) :
    shareOfThreePlanes quaternionTraceCubic F.centeredPlane G.centeredPlane H.centeredPlane =
      frameS F G H := by
  have hs := shareOfThreePlanes_eq_centered_frame_trace (J := traceInclusion)
    quaternionTraceCubic_round (Frame.centeredPlane_orthogonal hFG)
    (Frame.centeredPlane_orthogonal hFH) (Frame.centeredPlane_orthogonal hGH)
    F.centeredPlane_closed G.centeredPlane_closed F.centeredPlane_dimension
    quaternionFullCubic quaternionFullCubic_unit quaternionTraceCubic_apply
    (nativeCenteredTraceFrame F) (nativeCenteredTraceFrame G) (nativeCenteredTraceFrame H)
  rw [hs]
  simp only [nativeCenteredTraceFrame, quaternionFullCubic_apply, fullMat_ofMatrix,
    frameS, s, w, centeredTensor, traceForm]

/-- The actual paper share for three bases, defined using standalone native frame planes. -/
def basisGeometricShare (U V W : QBasis) : ℝ :=
  shareOfThreePlanes quaternionTraceCubic
    U.toFrame.centeredPlane V.toFrame.centeredPlane W.toFrame.centeredPlane

theorem basisGeometricShare_eq_basisS (U V W : QBasis)
    (hUV : U.MutuallyUnbiased V) (hUW : U.MutuallyUnbiased W)
    (hVW : V.MutuallyUnbiased W) :
    basisGeometricShare U V W = basisS U V W :=
  frameShare_eq_frameS U.toFrame V.toFrame W.toFrame
    ((U.mutuallyUnbiased_iff_toFrame V).mp hUV)
    ((U.mutuallyUnbiased_iff_toFrame W).mp hUW)
    ((V.mutuallyUnbiased_iff_toFrame W).mp hVW)

end

end QuaternionicMUB
