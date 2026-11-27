module

public import ThirteenPlanes.Quaternionic.NativeFrameShare
public import ThirteenPlanes.Quaternionic.SpectralTheorem
public import ThirteenPlanes.BinaryPlane

@[expose] public section

set_option backward.privateInPublic true

/-! The native quaternionic frame planes in both directions. -/

open scoped BigOperators RealInnerProductSpace

namespace QuaternionicMUB

open ThirteenPlanes ThirteenPlanes.RoundCubics SymmetricCubic

noncomputable section

theorem Frame.centeredPlane_orthogonal_iff (F G : Frame) :
    F.centeredPlane.IsOrtho G.centeredPlane ↔ F.MutuallyUnbiased G := by
  refine ⟨fun ho => ?_, Frame.centeredPlane_orthogonal⟩
  apply (Frame.mutuallyUnbiased_iff_centered_orthogonal F G).mpr
  intro a b
  rw [← F.centeredHilbert_inner G]
  exact ho.inner_eq (F.centeredHilbert_mem_plane a) (G.centeredHilbert_mem_plane b)

private theorem traceCubic_restriction_round (S : Submodule ℝ TracelessHilbert)
    (closed : IsClosedPiece quaternionTraceCubic S) :
    IsRound (quaternionTraceCubic.pullback (W := S) S.subtype) (1 / 6) := by
  refine ⟨by norm_num, fun x => ?_⟩
  let y : S := ⟨quaternionTraceCubic.L x x, closed x.property x.property⟩
  have hy : (quaternionTraceCubic.pullback (W := S) S.subtype).squareMap x = y := by
    apply ext_inner_right ℝ
    intro z
    change (quaternionTraceCubic.pullback (W := S) S.subtype).apply x x z =
      quaternionTraceCubic.apply x x z
    exact pullback_apply _ _ _ _ _
  rw [hy]
  exact quaternionTraceCubic_round.square_norm (x : TracelessHilbert)

private theorem spectral_mem_frame_plane (x : TracelessHilbert) (U : QBasis) (a : Outcome → ℝ)
    (hA : traceMat x = ∑ i, a i • U.point i) : x ∈ U.toFrame.centeredPlane := by
  have hsum : ∑ i, a i = 0 := by
    have h := congrArg rtrace hA
    rw [traceMat_trace] at h
    change 0 = rtraceLinear (∑ i, a i • U.point i) at h
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    have hp (i : Outcome) : rtraceLinear (U.point i) = 1 := U.point_trace_one i
    simp only [hp, mul_one] at h
    exact h.symm
  have hrep : x = ∑ i, a i • U.toFrame.centeredHilbert i := by
    apply traceMat_injective
    rw [hA, map_sum]
    simp only [map_smul, traceMat_centeredHilbert, Frame.centeredPointMatrix,
      QBasis.toFrame_point, smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [← Finset.sum_mul, hsum, zero_mul, zero_smul, sub_zero]
  rw [hrep]
  exact Submodule.sum_mem _ fun i _ =>
    U.toFrame.centeredPlane.smul_mem _ (U.toFrame.centeredHilbert_mem_plane i)

/-- Every closed quaternionic two-plane is the centered plane of an actual basis frame. -/
theorem closedPlane_has_frame (S : Submodule ℝ TracelessHilbert)
    (hdim : Module.finrank ℝ S = 2) (closed : IsClosedPiece quaternionTraceCubic S) :
    ∃ F : Frame, S = F.centeredPlane := by
  obtain ⟨_, z, hz⟩ := binaryPlaneNormalForm (traceCubic_restriction_round S closed) hdim
  let u : S := z.symm Complex.I
  let x : TracelessHilbert := (u : TracelessHilbert)
  have hu : ‖u‖ = 1 := by rw [show u = z.symm Complex.I from rfl, z.symm.norm_map, Complex.norm_I]
  have hx : ‖x‖ = 1 := hu
  have hzero : quaternionTraceCubic.apply x x x = 0 := by
    have he := hz u
    change _ = Real.sqrt (1 / 6 : ℝ) * ((z (z.symm Complex.I)) ^ 3).re at he
    rw [z.apply_symm_apply] at he
    have hi : (Complex.I ^ 3).re = 0 := by
      rw [pow_succ, pow_two, Complex.I_mul_I, neg_one_mul, Complex.neg_re, Complex.I_re, neg_zero]
    rw [hi, mul_zero, pullback_apply] at he
    exact he
  let y := quaternionTraceCubic.L x x
  have hyS : y ∈ S := closed u.property u.property
  have hy0 : y ≠ 0 := by
    intro hy
    have h := quaternionTraceCubic_round.square_norm x
    change ‖y‖ ^ 2 = _ at h
    rw [hy, norm_zero, hx] at h
    norm_num at h
  let v : S := ⟨‖y‖⁻¹ • y, S.smul_mem _ hyS⟩
  have hv : ‖v‖ = 1 := by
    change ‖‖y‖⁻¹ • y‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
  have huv : ⟪u, v⟫ = 0 := by
    change inner ℝ x (‖y‖⁻¹ • y) = 0
    have hxy : inner ℝ x y = 0 := (real_inner_comm y x).trans hzero
    calc
      _ = ‖y‖⁻¹ * inner ℝ x y := real_inner_smul_right x y _
      _ = _ := by rw [hxy, mul_zero]
  let b : Fin 2 → S := ![u, v]
  have hb : Orthonormal ℝ b := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · change inner ℝ u u = 1
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    · exact huv
    · exact (real_inner_comm u v).trans huv
    · change inner ℝ v v = 1
      rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ :=
    hb.linearIndependent.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])
  obtain ⟨U, a, _, hA⟩ := hermitian_projector_expansion (traceMat x) (traceMat_hermitian x)
  let F := U.toFrame
  have hxF : x ∈ F.centeredPlane := spectral_mem_frame_plane x U a hA
  have hyF : y ∈ F.centeredPlane := F.centeredPlane_closed hxF hxF
  have hbF : Submodule.span ℝ (Set.range b) ≤ F.centeredPlane.comap S.subtype := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hxF
    · exact F.centeredPlane.smul_mem _ hyF
  have hle : S ≤ F.centeredPlane := by
    intro w hw
    have hm : (⟨w, hw⟩ : S) ∈ Submodule.span ℝ (Set.range b) := by rw [hspan]; trivial
    exact hbF hm
  exact ⟨F, Submodule.eq_of_le_of_finrank_eq hle (hdim.trans F.centeredPlane_dimension.symm)⟩

end

end QuaternionicMUB
