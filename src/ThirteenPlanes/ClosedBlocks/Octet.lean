module

public import ThirteenPlanes.ClosedBlocks.ComplexWindow
public import ThirteenPlanes.ClosedBlocks.DecompositionPatterns
public import ThirteenPlanes.ClosedBlocks.OctetComplement

@[expose] public section

set_option backward.privateInPublic true

/-! The arbitrary embedded octet bound and its decomposition consequences. -/

open scoped Matrix RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce AlbertSequential.NativeAnalysis

noncomputable section

/-- The raw cubic on a harmonic closed eight-space is the actual complex trace cubic. -/
theorem nativeOctet_matrixEqualCubic {U : Submodule ℝ NativeTraceless}
    (closed : IsClosedPiece nativeEqualCubic U)
    (harmonic : (nativeEqualCubic.pullback (W := ↥U) U.subtype).TraceFree)
    (dim : Module.finrank ℝ U = 8) :
    ∃ I : U ≃ₗᵢ[ℝ] TracelessHermitian3,
      nativeEqualCubic.pullback (W := ↥U) U.subtype = matrixEqualCubic.pullback (W := ↥U) I.toLinearMap := by
  obtain ⟨I, he⟩ := harmonic_round_eight_cartan
    (closedSubspace_restriction_isRound Graded.nativeRound closed) harmonic dim
  refine ⟨I, ?_⟩
  have hs : Real.sqrt (1 / 6) * Real.sqrt 6 = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    norm_num
  apply SymmetricCubic.ext
  intro x y z
  have eq := congrArg (fun g : SymmetricCubic U => g.apply x y z) he
  simp only [SymmetricCubic.apply_smul, SymmetricCubic.pullback_apply, complexCartanCubic] at eq
  rw [← mul_assoc, hs, one_mul] at eq
  simpa only [SymmetricCubic.pullback_apply] using eq

/-- Every closed subspace orthogonal to an arbitrary embedded Albert octet has dimension at most two. -/
theorem nativeOctetComplement_finrank_le_two {U S : Submodule ℝ NativeTraceless}
    (hu : IsClosedPiece nativeEqualCubic U)
    (hc : (nativeEqualCubic.pullback (W := ↥U) U.subtype).TraceFree)
    (hd : Module.finrank ℝ U = 8)
    (hs : IsClosedPiece nativeEqualCubic S) (ho : U.IsOrtho S) :
    Module.finrank ℝ S ≤ 2 := by
  open AlbertSequential in
  obtain ⟨I, hI⟩ := nativeOctet_matrixEqualCubic hu hc hd
  open AlbertSequential in
  obtain ⟨W, hW⟩ := complexWindow_of_closedBlock hu I hI
  open AlbertSequential in
  obtain ⟨g, hg⟩ := native_complexWindow_conjugate_standard W
  let E := recoveredCoordinateEquiv
  let F : NativeTraceless →ₗ[ℝ] AlbertSequential.Albert :=
    g.linearEquiv.toLinearMap.comp (E.symm.toLinearMap.comp Glennie.traceLinear.ker.subtype)
  have hF : Function.Injective F :=
    g.linearEquiv.injective.comp (E.symm.injective.comp Glennie.traceLinear.ker.subtype_injective)
  have hF_apply (x : NativeTraceless) : F x = g.linearEquiv (E.symm x.val) := rfl
  let T := S.map F
  have horth : ∀ x ∈ T, ∀ y, AlbertSequential.standardComplexWindow.Contains y →
      AlbertSequential.tracePairing x y = 0 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨M, rfl⟩
    rw [hF_apply, ← hg, g.map_tracePairing, ← recoveredCoordinateEquiv_tracePairing, E.apply_symm_apply]
    let Z := E (W.embedding M)
    let z := nativeCenter Z
    have hz : z ∈ U := (hW z).mp (by
      refine ⟨M - (Glennie.trace Z / 3) • (1 : AlbertSequential.Hermitian3), ?_⟩
      apply E.injective
      rw [map_sub, map_smul, W.unit, map_sub, map_smul, recoveredCoordinateEquiv_unit, E.apply_symm_apply]
      rfl)
    have hh := ho.inner_eq hz hx
    change Glennie.inner (Glennie.traceless Z) x.val = 0 at hh
    rw [nativeInner_center_left] at hh
    change Glennie.inner x.val Z = 0
    rw [Glennie.inner_comm]
    exact hh
  have hsquare : ∀ x ∈ T, AlbertSequential.jordanMul x x -
      (AlbertSequential.albertTrace (AlbertSequential.jordanMul x x) / 3) • AlbertSequential.albertUnit ∈ T := by
    rintro _ ⟨x, hx, rfl⟩
    let z := nativeCenter (Glennie.jordan x.val x.val)
    have hz : z ∈ S := hs hx hx
    refine ⟨z, hz, ?_⟩
    let X := E.symm x.val
    let Z := AlbertSequential.jordanMul X X
    have hJ : E Z = Glennie.jordan x.val x.val := by
      change E (AlbertSequential.jordanMul (E.symm x.val) (E.symm x.val)) = _
      rw [recoveredCoordinateEquiv_jordanMul, E.apply_symm_apply]
    have hZ : E.symm z.val =
        Z - (AlbertSequential.albertTrace Z / 3) • AlbertSequential.albertUnit := by
      apply E.injective
      rw [E.apply_symm_apply, map_sub, map_smul, recoveredCoordinateEquiv_unit,
        ← recoveredCoordinateEquiv_trace, hJ]
      rfl
    rw [hF_apply z, hF_apply x, hZ, map_sub, map_smul, g.preserves_unit]
    rw [← g.preserves_product, g.preserves_trace]
  have hdim : Module.finrank ℝ T = Module.finrank ℝ S :=
    (S.equivMapOfInjective F hF).finrank_eq.symm
  rw [← hdim]
  exact standardOctetComplement_finrank_le_two T horth hsquare

private theorem matrixEqualCubic_traceFree : matrixEqualCubic.TraceFree := by
  obtain ⟨d, hd⟩ := exists_complex_four_plane_decomposition
  let P : PlaneDecomposition TracelessHermitian3 (Fin 4) :=
    ⟨d.piece, hd, d.orthogonal, d.exhaustive⟩
  have hr : IsRound matrixEqualCubic (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [matrixEqualCubic_squareMap, TracelessHermitian3.square_norm_sq]
    ring
  have hc : IsClosedPlaneSystem matrixEqualCubic P := fun i =>
    (isClosedPiece_smul_iff (by positivity : Real.sqrt 6 ≠ 0) (d.piece i)).mp (d.closed i)
  exact traceFree_of_isClosedPlaneSystem hr hc

/-- The octet complement bound stated directly for copies of the raw complex trace cubic. -/
theorem nativeOctetComplement_finrank_le_two_of_trace_isometry {U S : Submodule ℝ NativeTraceless}
    (hu : IsClosedPiece nativeEqualCubic U) (hs : IsClosedPiece nativeEqualCubic S) (ho : U.IsOrtho S)
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3)
    (hI : nativeEqualCubic.pullback (W := ↥U) U.subtype =
      matrixEqualCubic.pullback (W := ↥U) I.toLinearMap) :
    Module.finrank ℝ S ≤ 2 := by
  have htf : (nativeEqualCubic.pullback (W := ↥U) U.subtype).TraceFree := by
    rw [hI]
    have hh := @traceFree_pullback_iff ↥U TracelessHermitian3
      inferInstance (Submodule.innerProductSpace U) inferInstance
      inferInstance (inferInstance : InnerProductSpace ℝ TracelessHermitian3) matrixEqualCubic I
    exact hh.mpr matrixEqualCubic_traceFree
  have hd : Module.finrank ℝ U = 8 := I.toLinearEquiv.finrank_eq.trans (by
    simpa using Peirce.finrank_eq_twice_card fourPlaneDecomposition)
  exact nativeOctetComplement_finrank_le_two hu htf hd hs ho

/-- Proposition octet on the actual native model. -/
theorem complementsOfOctet :
    (∀ U S : Submodule ℝ NativeTraceless, IsClosedPiece nativeEqualCubic U →
      (nativeEqualCubic.pullback (W := ↥U) U.subtype).TraceFree → Module.finrank ℝ U = 8 →
      IsClosedPiece nativeEqualCubic S → U.IsOrtho S → Module.finrank ℝ S ≤ 2) ∧
    (∀ {ι : Type*} [Fintype ι] (d : Decomposition nativeEqualCubic ι) (i : ι),
      Module.finrank ℝ (d.piece i) = 8 →
      Fintype.card ι = 10 ∧ ∀ j, j ≠ i → Module.finrank ℝ (d.piece j) = 2) ∧
    (∃ d : Decomposition nativeEqualCubic (Fin 10),
      Module.finrank ℝ (d.piece 0) = 8 ∧
      (∀ i : Fin 10, i ≠ 0 → Module.finrank ℝ (d.piece i) = 2) ∧
      ∃ I : d.piece 0 ≃ₗᵢ[ℝ] TracelessHermitian3,
        nativeEqualCubic.pullback (W := ↥(d.piece 0)) (d.piece 0).subtype =
          matrixEqualCubic.pullback (W := ↥(d.piece 0)) I.toLinearMap) := by
  have htf : nativeEqualCubic.TraceFree :=
    traceFree_of_isClosedPlaneSystem Graded.nativeRound Graded.labelledClosedPlanes
  refine ⟨fun _ _ => nativeOctetComplement_finrank_le_two, ?_, ?_⟩
  · intro ι _ d i hi
    have hti := (closedPieces_traceFree_iff d.orthogonal d.exhaustive d.closed).mp htf i
    exact d.octet_has_nine_other_planes Graded.nativeRound htf nativeTraceless_finrank i hi
      (fun S hS ho => nativeOctetComplement_finrank_le_two (d.closed i) hti hi hS ho)
  · obtain ⟨d, hi, ho, _⟩ := exists_nativeAlbert_octet_nine_planes
    have hti := (closedPieces_traceFree_iff d.orthogonal d.exhaustive d.closed).mp htf 0
    exact ⟨d, hi, ho, nativeOctet_matrixEqualCubic (d.closed 0) hti hi⟩

end

end ThirteenPlanes.ClosedBlocks
