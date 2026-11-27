module

public import ThirteenPlanes.JordanFrames.ComplexFourFrameNormalization
public import ThirteenPlanes.AlbertGrading.Contrast.Checks

@[expose] public section

set_option backward.privateInPublic true

/-! The four-plane unitary classification applied to the literal ordered Weyl frames. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace ThirteenPlanes.AlbertGrading.Contrast

open RoundCubics JordanFrames Graded

noncomputable section

set_option maxHeartbeats 950000

private def asComplexTraceFrame (F : Fin 3 → FullHermitian3) (hF : HermFrame F) : ComplexTraceFrame3 where
  point i := (F i).val
  hermitian i := (F i).property
  trace_one i := by
    rw [hermitian_trace_eq_real (F i).property, hF.trace_one i, Complex.ofReal_one]
  jordan_point i j := by
    by_cases h : i = j
    · subst j
      rw [ite_eq_left rfl]
      exact congrArg Subtype.val (hF.idempotent i)
    · rw [ite_eq_right h]
      exact congrArg Subtype.val (hF.orthogonal i j h)
  sum_unit := by
    rw [Fin.sum_univ_three]
    exact congrArg Subtype.val hF.sum_unit

private theorem normalize_hermitian_frames (F : Fin 4 → Fin 3 → FullHermitian3)
    (hF : ∀ i, HermFrame (F i)) (hO : ∀ i j, i ≠ j → HermUnbiased (F i) (F j)) :
    ∃ (U : Matrix.unitaryGroup (Fin 3) ℂ) (π : Equiv.Perm (Fin 4)),
      ∀ i, (conjugateComplexFrame U (asComplexTraceFrame (F i) (hF i))).plane = matrixPlane (π i) := by
  apply normalize_complex_frames
  intro i j hij a b
  rw [tracePairing_eq_re_trace_jordan]
  exact hO i j hij a b

/-- One unitary and the actual outcome permutations carry any four unbiased frames to the Weyl frames. -/
theorem qutritFourFrames_fromNativeFrames : FrameProperties.QutritFourFrames := by
  intro F hF hO
  obtain ⟨U, τ, hU⟩ := normalize_hermitian_frames F hF hO
  obtain ⟨V, η, hV⟩ := normalize_hermitian_frames weylEigenframe weylEigenframe_frame weylEigenframe_unbiased
  let π : Equiv.Perm (Fin 4) := τ.trans η.symm
  have same (i : Fin 4) :
      (conjugateComplexFrame U (asComplexTraceFrame (F i) (hF i))).plane =
        (conjugateComplexFrame V (asComplexTraceFrame (weylEigenframe (π i)) (weylEigenframe_frame (π i)))).plane := by
    rw [hU i, hV (π i)]
    simp [π]
  choose σ hσ using fun i => (complex_framePlane_eq_iff_relabel _ _).mp (same i).symm
  let W : Matrix.unitaryGroup (Fin 3) ℂ := star V * U
  refine ⟨W.val, W.property, π, σ, fun i a => ?_⟩
  change complexConjugate (star V * U) (F i a).val = _
  rw [Unitary.conjStarAlgAut_mul_apply]
  have he := hσ i a
  change complexConjugate U (F i a).val = complexConjugate V (weylEigenframe (π i) (σ i a)).val at he
  rw [he, ← Unitary.conjStarAlgAut_symm, StarAlgEquiv.symm_apply_apply]

/-- The qutrit contrast table after applying the four-frame theorem. -/
theorem qutritContrastTable_fromNativeFrames : Statements.QutritContrastTable := qutritContrastTable qutritFourFrames_fromNativeFrames

end

end ThirteenPlanes.AlbertGrading.Contrast
