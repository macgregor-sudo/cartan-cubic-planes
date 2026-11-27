module

public import ThirteenPlanes.JordanFrames.Generic
public import ThirteenPlanes.Quaternionic.ClosedFramePlanes
public import ThirteenPlanes.Quaternionic.FrameDictionary
public import ThirteenPlanes.Quaternionic.BasisReduction

@[expose] public section

set_option backward.privateInPublic true

/-! The frame-plane dictionary and pair normal form on actual quaternionic matrices. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics QuaternionicMUB

noncomputable section

private def quaternionicJordan : QMat →ₗ[ℝ] QMat →ₗ[ℝ] QMat :=
  (1 / 2 : ℝ) • (LinearMap.mul ℝ QMat + (LinearMap.mul ℝ QMat).flip)

private theorem quaternionicJordan_apply (X Y : QMat) :
    quaternionicJordan X Y = jordan X Y := rfl

private theorem quaternionicFrame_mul (F : Frame) (i j : Outcome) :
    quaternionicJordan (F.point i) (F.point j) = if i = j then F.point i else 0 := by
  rw [quaternionicJordan_apply]
  split_ifs with h
  · subst j
    exact F.idempotent i
  · exact F.orthogonal i j h

/-- Equality of centered quaternionic planes is equality of their actual projectors up to permutation. -/
theorem quaternionic_framePlane_eq_iff_relabel (F G : Frame) :
    F.centeredPlane = G.centeredPlane ↔
      ∃ σ : Equiv.Perm Outcome, ∀ i, G.point i = F.point (σ i) := by
  constructor
  · intro heq
    have h := congrArg (fun U : Submodule ℝ TracelessHilbert => U.map traceMat) heq
    simp only [Frame.centeredPlane, Submodule.map_span, ← Set.range_comp] at h
    have hc (H : Frame) :
        traceMat ∘ H.centeredHilbert = fun i => H.point i - (1 / 3 : ℝ) • (1 : QMat) :=
      funext fun i => traceMat_centeredHilbert H i
    rw [hc F, hc G] at h
    exact relabel_of_centered_span_eq quaternionicJordan rtraceLinear 1 F.trace_one G.trace_one
      (quaternionicFrame_mul F) (quaternionicFrame_mul G) F.sum_points h
  · rintro ⟨σ, hσ⟩
    have hc (i : Outcome) : G.centeredHilbert i = F.centeredHilbert (σ i) := by
      apply traceMat_injective
      simp only [traceMat_centeredHilbert, Frame.centeredPointMatrix, hσ]
    change Submodule.span ℝ (Set.range F.centeredHilbert) =
      Submodule.span ℝ (Set.range G.centeredHilbert)
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact ⟨σ.symm i, by rw [hc, σ.apply_symm_apply]⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨σ i, (hc i).symm⟩

/-- A closed two-plane of the quaternionic trace-zero space has a unique frame up to relabeling. -/
theorem quaternionic_closedPlane_iff_frame (S : Submodule ℝ TracelessHilbert)
    (dim : Module.finrank ℝ S = 2) :
    IsClosedPiece quaternionTraceCubic S ↔
      ∃ F : Frame, S = F.centeredPlane ∧ ∀ G : Frame, S = G.centeredPlane →
        ∃ σ : Equiv.Perm Outcome, ∀ i, G.point i = F.point (σ i) := by
  constructor
  · intro hS
    obtain ⟨F, hF⟩ := closedPlane_has_frame S dim hS
    exact ⟨F, hF, fun G hG => (quaternionic_framePlane_eq_iff_relabel F G).mp (hF.symm.trans hG)⟩
  · rintro ⟨F, rfl, _⟩
    exact F.centeredPlane_closed

/-- Pairwise unbiased quaternionic frame sets satisfy the dimension count. -/
theorem quaternionic_frameSet_capacity (S : Set Frame) (orth : S.Pairwise Frame.MutuallyUnbiased) :
    S.Finite ∧ S.ncard ≤ 7 ∧ ((⨆ f : S, f.val.centeredPlane) = ⊤ ↔ S.ncard = 7) :=
  orthogonalPlaneSet_capacity finrank_TracelessHilbert Frame.centeredPlane
    Frame.centeredPlane_dimension S
    (fun f hf g hg hfg => (f.centeredPlane_orthogonal_iff g).mpr (orth hf hg hfg))

/-- A complete system of closed quaternionic planes would have seven planes. -/
theorem quaternionic_completePlane_count {ι : Type*} [Fintype ι]
    (P : PlaneDecomposition TracelessHilbert ι) :
    Fintype.card ι = 7 :=
  (orthogonalPlaneFamily_capacity finrank_TracelessHilbert P.plane P.dimension
    P.pairwise_orthogonal).2.mp P.exhaustive

/-- A single unitary conjugation carries an arbitrary pair of unbiased quaternionic
frames to the coordinate and Fourier projectors. -/
theorem quaternionic_normalize_unbiased_pair (F G : Frame) (h : F.MutuallyUnbiased G) :
    ∃ U : QBasis, (∀ i, unitaryConjugate U (F.point i) = QBasis.coordinate.point i) ∧
      (∀ i, unitaryConjugate U (G.point i) = fourierBasis.point i) := by
  obtain ⟨A, hA⟩ := frame_has_basis F
  obtain ⟨B, hB⟩ := frame_has_basis G
  have hAB : A.MutuallyUnbiased B := by
    rw [QBasis.mutuallyUnbiased_iff_trace]
    intro i j
    rw [hA, hB]
    exact h i j
  let B₀ := A.transport B
  have hB₀ : QBasis.coordinate.MutuallyUnbiased B₀ := by
    simpa only [B₀, A.transport_self] using (A.transport_mutuallyUnbiased A B).mpr hAB
  obtain ⟨p, q, hp, hq, hnorm⟩ := hadamard_normal_form B₀ hB₀
  let D := diagonalBasis p hp
  let U := A.product D.adjoint
  have hconj (X : QMat) : unitaryConjugate U X =
      unitaryConjugate D.adjoint (unitaryConjugate A X) := by
    simp only [U, unitaryConjugate, QBasis.product_mat, Matrix.conjTranspose_mul, mul_assoc]
  refine ⟨U, ?_, ?_⟩
  · intro i
    rw [← hA, hconj, ← QBasis.transport_point, A.transport_self, ← QBasis.transport_point]
    change (D.product QBasis.coordinate).point i = _
    rw [D.product_coordinate]
    exact diagonalBasis_point p hp i
  · intro i
    rw [← hB, hconj, ← QBasis.transport_point, ← QBasis.transport_point]
    change (D.product B₀).point i = _
    rw [← QBasis.rightPhases_point (D.product B₀) q hq, hnorm]

end
end ThirteenPlanes.JordanFrames
