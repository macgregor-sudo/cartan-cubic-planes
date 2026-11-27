module

public import ThirteenPlanes.FourPlaneUnitary
public import ThirteenPlanes.JordanFrames.ComplexPair
public import ThirteenPlanes.Fields.ComplexFrames
public import ThirteenPlanes.Shares.ComplexFourPlanes

@[expose] public section

set_option backward.privateInPublic true

/-! Unitary uniqueness of the complex Cartan four-plane decomposition. -/

namespace ThirteenPlanes.RoundCubics

open JordanFrames

noncomputable section

private theorem closed_pullback_of_cubic_invariance {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type*} {h : SymmetricCubic V}
    {P : PlaneDecomposition V ι} (I : V ≃ₗᵢ[ℝ] V) (hi : h.pullback I.toLinearMap = h)
    (cP : IsClosedPlaneSystem h P) : IsClosedPlaneSystem h (pullbackPlaneSystem P I) :=
  Eq.mp (congrArg (fun k : SymmetricCubic V => IsClosedPlaneSystem k (pullbackPlaneSystem P I)) hi)
    (IsClosedPlaneSystem.pullback_isometry cP I)

private abbrev referencePullback (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    PlaneDecomposition TracelessHermitian3 (Fin 4) :=
  pullbackPlaneSystem (V := TracelessHermitian3) (W := TracelessHermitian3) fourPlaneDecomposition (unitaryTraceIsometry U)

private theorem referencePullback_mem (U : Matrix.unitaryGroup (Fin 3) ℂ) (i : Fin 4) (x : TracelessHermitian3) :
    x ∈ (referencePullback U).plane i ↔ unitaryTraceIsometry U x ∈ matrixPlane i := by
  with_reducible
    exact mem_pullbackPlaneSystem (V := TracelessHermitian3) (W := TracelessHermitian3)
      fourPlaneDecomposition (unitaryTraceIsometry U) i x

private theorem referencePullback_closed (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    IsClosedPlaneSystem matrixEqualCubic (referencePullback U) :=
  closed_pullback_of_cubic_invariance (h := matrixEqualCubic) (P := fourPlaneDecomposition)
    (unitaryTraceIsometry U) (unitaryTraceIsometry_preserves_cubic U) PencilFlow.Proofs.fourPlaneCubic_isClosedPlaneSystem

private theorem normalize_first_pair (R : PlaneDecomposition TracelessHermitian3 (Fin 4))
    (cR : IsClosedPlaneSystem matrixEqualCubic R) :
    ∃ U : Matrix.unitaryGroup (Fin 3) ℂ,
      R.plane 0 = (referencePullback U).plane 0 ∧ R.plane 1 = (referencePullback U).plane 1 := by
  obtain ⟨F, hF⟩ := complexClosedPlane_has_frame (R.plane 0) (R.dimension 0) (cR 0)
  obtain ⟨G, hG⟩ := complexClosedPlane_has_frame (R.plane 1) (R.dimension 1) (cR 1)
  have orth : (R.plane 0).IsOrtho (R.plane 1) := R.pairwise_orthogonal (by decide : (0 : Fin 4) ≠ 1)
  rw [hF, hG] at orth
  obtain ⟨U, σ, τ, hU, hV⟩ := complex_normalize_unbiased_pair F G
    ((complex_framePlane_orthogonal_iff F G).mp orth)
  exact ⟨U, hF.trans (unitary_framePlane_eq_reference F U 0 σ hU),
    hG.trans (unitary_framePlane_eq_reference G U 1 τ hV)⟩

private theorem normalize_four_planes (R : PlaneDecomposition TracelessHermitian3 (Fin 4))
    (cR : IsClosedPlaneSystem matrixEqualCubic R) :
    ∃ (U : Matrix.unitaryGroup (Fin 3) ℂ) (π : Equiv.Perm (Fin 4)),
      ∀ i, R.plane i = (referencePullback U).plane (π i) := by
  obtain ⟨U, first, second⟩ := normalize_first_pair R cR
  obtain ⟨π, _, _, planes⟩ := fourPlane_completion_unique (V := TracelessHermitian3)
    (h := matrixEqualCubic) (c := 1 / 6) (P := R) (Q := referencePullback U)
    PencilFlow.Proofs.fourPlaneCubic_isRound cR (referencePullback_closed U) first second
  exact ⟨U, π, planes⟩

/-- Any complete system of closed planes in the traceless Hermitian model is
carried to the four standard mutually unbiased frame planes by one unitary. -/
/- Brierley, Weigert and Bengtsson classify mutually unbiased bases in dimension three
(arXiv:0907.4097v2, §2.2, Eqs. (6)–(11)). The proof here normalizes the first pair to
the standard and Fourier frames and uses closed-plane multiplication to determine the
remaining pair up to interchange. -/
theorem complex_closedPlaneSystem_unitary {ι : Type*} [Fintype ι]
    (P : PlaneDecomposition TracelessHermitian3 ι) (closed : IsClosedPlaneSystem matrixEqualCubic P) :
    ∃ (U : Matrix.unitaryGroup (Fin 3) ℂ) (π : ι ≃ Fin 4), ∀ i x,
      x ∈ P.plane i ↔ unitaryTraceIsometry U x ∈ matrixPlane (π i) := by
  let e : ι ≃ Fin 4 := Fintype.equivFinOfCardEq (complex_closedPlaneSystem_four P closed).1
  let R := reindexPlaneSystem P e.symm
  obtain ⟨U, π, planes⟩ := normalize_four_planes R (fun i => closed (e.symm i))
  refine ⟨U, e.trans π, fun i x => ?_⟩
  have he : R.plane (e i) = P.plane i := by
    change P.plane (e.symm (e i)) = _
    rw [e.symm_apply_apply]
  have same : P.plane i = (referencePullback U).plane (π (e i)) := he.symm.trans (planes (e i))
  have hm : x ∈ P.plane i ↔ x ∈ (referencePullback U).plane (π (e i)) :=
    Iff.of_eq (congrArg (fun S : Submodule ℝ TracelessHermitian3 => x ∈ S) same)
  change x ∈ P.plane i ↔ unitaryTraceIsometry U x ∈ matrixPlane (π (e i))
  exact hm.trans (referencePullback_mem U (π (e i)) x)

end

end ThirteenPlanes.RoundCubics
