module

public import ThirteenPlanes.Quaternionic.SquareSum
public import ThirteenPlanes.Quaternionic.DiagonalPlane
public import ThirteenPlanes.Quaternionic.Completion

@[expose] public section

/-! Native six-frame completion in the actual traceless quaternionic matrix space. -/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma Frame.centered_inner_zero_of_plane (F : Frame) (v : TracelessHilbert)
    (hv : ∀ k, inner ℝ v (F.planeOrtho k) = 0) (a : Outcome) :
    inner ℝ v (F.centeredHilbert a) = 0 := by
  have hs := F.centered_parseval v
  simp only [hv, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hs
  have hn := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    sq_nonneg (inner ℝ v (F.centeredHilbert i))) (Finset.mem_univ a)
  have hsq : inner ℝ v (F.centeredHilbert a) ^ 2 = 0 := by
    rw [hs] at hn
    exact le_antisymm hn (sq_nonneg _)
  exact sq_eq_zero_iff.mp hsq

def sixPlaneSpan (F : Fin 6 → Frame) : Submodule ℝ TracelessHilbert :=
  Submodule.span ℝ (Set.range (fun ia : Fin 6 × Fin 2 => (F ia.1).planeOrtho ia.2))

lemma sixPlaneSpan_finrank (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    Module.finrank ℝ (sixPlaneSpan F) = 12 := by
  unfold sixPlaneSpan
  have h := _root_.finrank_span_eq_card (mub_planes_orthonormal F hF).linearIndependent
  exact h.trans (by norm_num)

lemma sixPlaneSpan_orthogonal_finrank (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    Module.finrank ℝ (sixPlaneSpan F)ᗮ = 2 := by
  apply Submodule.finrank_add_finrank_orthogonal'
  rw [sixPlaneSpan_finrank F hF, finrank_TracelessHilbert]

def sixComplementBasis (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    OrthonormalBasis (Fin 2) ℝ (sixPlaneSpan F)ᗮ :=
  (stdOrthonormalBasis ℝ (sixPlaneSpan F)ᗮ).reindex
    (finCongr (sixPlaneSpan_orthogonal_finrank F hF))

def sixFullFamily (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    (Fin 6 × Fin 2) ⊕ Fin 2 → TracelessHilbert :=
  Sum.elim (fun ia => (F ia.1).planeOrtho ia.2)
    (fun k => (sixComplementBasis F hF k).val)

lemma sixFullFamily_orthonormal (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    Orthonormal ℝ (sixFullFamily F hF) := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl ia =>
    cases j with
    | inl ja => simpa only [sixFullFamily, Sum.elim_inl, Sum.inl.injEq] using
        (orthonormal_iff_ite.mp (mub_planes_orthonormal F hF)) ia ja
    | inr k =>
      have h := (sixPlaneSpan F).inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self ia)) (sixComplementBasis F hF k).property
      simpa only [sixFullFamily, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false] using h
  | inr k =>
    cases j with
    | inl ia =>
      have h := (sixPlaneSpan F).inner_left_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self ia)) (sixComplementBasis F hF k).property
      simpa only [sixFullFamily, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false] using h
    | inr l =>
      change inner ℝ (sixComplementBasis F hF k) (sixComplementBasis F hF l) = _
      simpa only [Sum.inr.injEq] using (sixComplementBasis F hF).inner_eq_ite k l

def sixFullBasis (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    OrthonormalBasis ((Fin 6 × Fin 2) ⊕ Fin 2) ℝ TracelessHilbert :=
  OrthonormalBasis.mk (sixFullFamily_orthonormal F hF)
    ((sixFullFamily_orthonormal F hF).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [finrank_TracelessHilbert])).ge

lemma sixComplement_square_sum (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    nativeTracelessMatrix (sixComplementBasis F hF 0).val ^ 2 +
      nativeTracelessMatrix (sixComplementBasis F hF 1).val ^ 2 =
      (2 / 3 : ℝ) • (1 : QMat) := by
  have h := nativeTraceless_square_sum (sixFullBasis F hF)
  simp only [sixFullBasis, OrthonormalBasis.coe_mk, sixFullFamily, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr] at h
  have hp : (∑ ia : Fin 6 × Fin 2, nativeTracelessMatrix ((F ia.1).planeOrtho ia.2) ^ 2) =
      (4 : ℝ) • (1 : QMat) := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, nativeTracelessMatrix_apply, Frame.planeOrtho_square_sum]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    module
  rw [hp, Fin.sum_univ_two] at h
  calc
    _ = (14 / 3 : ℝ) • (1 : QMat) - (4 : ℝ) • (1 : QMat) := by
      exact eq_sub_of_add_eq' h
    _ = _ := by module

lemma nativeTracelessMatrix_hermitian (v : TracelessHilbert) :
    (nativeTracelessMatrix v).IsHermitian := v.property.1
lemma nativeTracelessMatrix_trace_zero (v : TracelessHilbert) :
    rtrace (nativeTracelessMatrix v) = 0 := v.property.2

def traceFormRightLinear (A : QMat) : QMat →ₗ[ℝ] ℝ where
  toFun B := traceForm A B
  map_add' B C := traceForm_add_right A B C
  map_smul' r B := by simp only [traceForm_smul_right, RingHom.id_apply, smul_eq_mul]

/-- Every six pairwise unbiased ordinary quaternionic frames admit an actual
seventh frame. There is no spectral, completion, or normal-form premise. -/
theorem six_frames_extend (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    ∃ U : QBasis, ∀ i, (F i).MutuallyUnbiased U.toFrame := by
  let b := sixComplementBasis F hF
  let X := nativeTracelessMatrix (b 0).val
  let Y := nativeTracelessMatrix (b 1).val
  have hXX : traceForm X X = 1 := by
    rw [← nativeTracelessMatrix_inner]
    exact b.inner_eq_one 0
  have hYY : traceForm Y Y = 1 := by
    rw [← nativeTracelessMatrix_inner]
    exact b.inner_eq_one 1
  have hXY : traceForm X Y = 0 := by
    rw [← nativeTracelessMatrix_inner]
    exact b.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)
  have hComm : Commute X Y := square_sum_pair_commutes X Y
    (nativeTracelessMatrix_hermitian _) (nativeTracelessMatrix_hermitian _)
    (nativeTracelessMatrix_trace_zero _) (nativeTracelessMatrix_trace_zero _)
    hXX hYY hXY (sixComplement_square_sum F hF)
  obtain ⟨U, hU⟩ := commuting_orthonormal_traceless_diagonal_plane X Y
    (nativeTracelessMatrix_hermitian _) (nativeTracelessMatrix_hermitian _)
    (nativeTracelessMatrix_trace_zero _) (nativeTracelessMatrix_trace_zero _)
    hXX hYY hXY hComm
  refine ⟨U, ?_⟩
  intro i
  apply ((F i).mutuallyUnbiased_iff_centered_orthogonal U.toFrame).mpr
  intro a c
  have hz (k : Fin 2) : traceForm ((F i).centeredPointMatrix a)
      (nativeTracelessMatrix (b k).val) = 0 := by
    have hc : inner ℝ (b k).val ((F i).centeredHilbert a) = 0 := by
      apply Frame.centered_inner_zero_of_plane
      intro j
      exact (sixPlaneSpan F).inner_left_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (i,j))) (b k).property
    rw [real_inner_comm, nativeTracelessMatrix_inner,
      nativeTracelessMatrix_apply, Frame.centeredHilbert_matrix] at hc
    exact hc
  have hm : Submodule.span ℝ ({X,Y} : Set QMat) ≤
      (traceFormRightLinear ((F i).centeredPointMatrix a)).ker := by
    apply Submodule.span_le.mpr
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with rfl | rfl
    · exact hz 0
    · exact hz 1
  have hu : U.toFrame.centeredPointMatrix c ∈ Submodule.span ℝ ({X,Y} : Set QMat) := by
    rw [← hU]
    exact Submodule.subset_span (Set.mem_range_self c)
  exact hm hu

/-- Basis-level six-completion, obtained from literal column projectors. -/
theorem six_bases_extend (B : Fin 6 → QBasis) (hB : IsMUBFamily B) :
    ∃ U : QBasis, ∀ i, (B i).MutuallyUnbiased U := by
  have hF : IsMUBFrameFamily (fun i => (B i).toFrame) := by
    intro i j hij
    exact ((B i).mutuallyUnbiased_iff_toFrame (B j)).mp (hB hij)
  obtain ⟨U, hU⟩ := six_frames_extend (fun i => (B i).toFrame) hF
  exact ⟨U, fun i => ((B i).mutuallyUnbiased_iff_toFrame U).mpr (hU i)⟩

end QuaternionicMUB
