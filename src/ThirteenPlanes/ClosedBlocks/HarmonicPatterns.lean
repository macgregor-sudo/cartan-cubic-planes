module

public import ThirteenPlanes.ClosedBlocks.Octet
public import ThirteenPlanes.ClosedBlocks.ModelDimensions

@[expose] public section

set_option backward.privateInPublic true

/-! Transport the native orthogonality obstructions back to arbitrary harmonic round forms. -/

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce

noncomputable section

/-- Two real Cartan blocks in the native Albert model cannot be orthogonal. -/
def NativeNoTwoFives : Prop :=
  ∀ U S : Submodule ℝ NativeTraceless, IsClosedPiece nativeEqualCubic U →
    IsClosedPiece nativeEqualCubic S → U.IsOrtho S →
    (nativeEqualCubic.pullback (W := ↥U) U.subtype).TraceFree →
    (nativeEqualCubic.pullback (W := ↥S) S.subtype).TraceFree →
    Module.finrank ℝ U = 5 → Module.finrank ℝ S ≠ 5

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : SymmetricCubic V} {c : ℝ} {ι : Type*} [Fintype ι]

set_option maxHeartbeats 500000 in
private theorem map_closed_harmonic_block
    (I : V ≃ₗᵢ[ℝ] NativeTraceless) {t : ℝ} (ht : t ≠ 0)
    (hI : h = t • nativeEqualCubic.pullback I.toLinearMap)
    (U : Submodule ℝ V) (closed : IsClosedPiece h U) :
    IsClosedPiece nativeEqualCubic (U.map I.toLinearMap) ∧
      ((h.pullback U.subtype).TraceFree →
        (nativeEqualCubic.pullback (W := ↥(U.map I.toLinearMap)) (U.map I.toLinearMap).subtype).TraceFree) := by
  let A := U.map I.toLinearMap
  let J := mapBlockIsometry I U
  let B : SymmetricCubic A := nativeEqualCubic.pullback (W := ↥A) A.subtype
  have hp : h = (t • nativeEqualCubic).pullback I.toLinearMap :=
    hI.trans (pullback_smul_cubic nativeEqualCubic I.toLinearMap t).symm
  have hc : IsClosedPiece (t • nativeEqualCubic) A := isClosedPiece_map_isometry I hp closed
  refine ⟨(isClosedPiece_smul_iff ht A).mp hc, fun tf => ?_⟩
  have he : h.pullback U.subtype = t • B.pullback (W := ↥U) J.toLinearMap := by
    rw [hI, pullback_smul_cubic, pullback_block_map]
  have htf : (t • B.pullback (W := ↥U) J.toLinearMap).TraceFree := he ▸ tf
  have htf' : (B.pullback (W := ↥U) J.toLinearMap).TraceFree :=
    (traceFree_smul_iff _ ht).mp htf
  exact (traceFree_pullback_iff (V := ↥U) (W := ↥A) B J).mp htf'

/-- The allowed proper harmonic round decomposition patterns on the actual block spaces. -/
def HarmonicBlockDecompositionPattern (c : ℝ) (d : Decomposition h ι) : Prop :=
    (Module.finrank ℝ V = 8 ∧ Fintype.card ι = 4 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∨
      (Module.finrank ℝ V = 26 ∧
        ((Fintype.card ι = 13 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∨
         (Fintype.card ι = 10 ∧ ∃ i, Module.finrank ℝ (d.piece i) = 8 ∧
           (∀ j, j ≠ i → Module.finrank ℝ (d.piece j) = 2) ∧
           ∃ I : d.piece i ≃ₗᵢ[ℝ] TracelessHermitian3,
             h.pullback (d.piece i).subtype =
               Real.sqrt c • complexCartanCubic.pullback (W := ↥(d.piece i)) I.toLinearMap)))

/-- The harmonic classification follows on the actual original block spaces
from excluding an orthogonal pair of real Cartan blocks in the native model. -/
theorem classifyHarmonicRoundDecompositions_of_noTwoFives
    (hno : NativeNoTwoFives) (d : Decomposition h ι)
    (round : IsRound h c) (tf : h.TraceFree) (proper : 1 < Fintype.card ι) :
    HarmonicBlockDecompositionPattern c d := by
  unfold HarmonicBlockDecompositionPattern
  apply classifyHarmonicRoundDecompositions_of_orthogonal_exclusions d round tf proper
  · intro hV U S hU hS ho hu h8
    obtain ⟨I, hI⟩ := harmonic_round_twentySix_albert round tf hV
    have hs : 0 < Real.sqrt c * Real.sqrt 6 := mul_pos (Real.sqrt_pos.mpr round.positive) (by positivity)
    obtain ⟨hcU, htU⟩ := map_closed_harmonic_block I hs.ne' hI U hU
    obtain ⟨hcS, _⟩ := map_closed_harmonic_block I hs.ne' hI S hS
    have dU := (mapBlockIsometry I U).toLinearEquiv.finrank_eq
    have dS := (mapBlockIsometry I S).toLinearEquiv.finrank_eq
    have hb := nativeOctetComplement_finrank_le_two hcU (htU hu) (dU.symm.trans h8) hcS
      (isOrtho_map_isometry I ho)
    omega
  · intro hV U S hU hS ho hu hs h5 hs5
    obtain ⟨I, hI⟩ := harmonic_round_twentySix_albert round tf hV
    have hr : 0 < Real.sqrt c * Real.sqrt 6 := mul_pos (Real.sqrt_pos.mpr round.positive) (by positivity)
    obtain ⟨hcU, htU⟩ := map_closed_harmonic_block I hr.ne' hI U hU
    obtain ⟨hcS, htS⟩ := map_closed_harmonic_block I hr.ne' hI S hS
    refine hno _ _ hcU hcS (isOrtho_map_isometry I ho) (htU hu) (htS hs)
      ((mapBlockIsometry I U).toLinearEquiv.finrank_eq.symm.trans h5)
      ((mapBlockIsometry I S).toLinearEquiv.finrank_eq.symm.trans hs5)

end

/-- The abstract classification imposes the exact patterns on the given native decomposition. -/
theorem nativeModel_closedBlocks_of_noTwoFives {ι : Type*} [Fintype ι]
    (hno : NativeNoTwoFives) (d : Decomposition nativeEqualCubic ι) (hp : 1 < Fintype.card ι) :
    (Fintype.card ι = 13 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∨
      (Fintype.card ι = 10 ∧ ∃ i, Module.finrank ℝ (d.piece i) = 8 ∧
        (∀ j, j ≠ i → Module.finrank ℝ (d.piece j) = 2) ∧
        ∃ I : d.piece i ≃ₗᵢ[ℝ] TracelessHermitian3,
          nativeEqualCubic.pullback (W := ↥(d.piece i)) (d.piece i).subtype =
            matrixEqualCubic.pullback (W := ↥(d.piece i)) I.toLinearMap) := by
  have htf : nativeEqualCubic.TraceFree :=
    traceFree_of_isClosedPlaneSystem Graded.nativeRound Graded.labelledClosedPlanes
  have hr := classifyHarmonicRoundDecompositions_of_noTwoFives hno d Graded.nativeRound htf hp
  unfold HarmonicBlockDecompositionPattern at hr
  rcases hr with ⟨h8, _⟩ | ⟨_, h13 | ⟨hc, i, hi, hj, _⟩⟩
  · have h26 := nativeTraceless_finrank
    omega
  · exact Or.inl h13
  · have hti := (closedPieces_traceFree_iff d.orthogonal d.exhaustive d.closed).mp htf i
    exact Or.inr ⟨hc, i, hi, hj, nativeOctet_matrixEqualCubic (d.closed i) hti hi⟩

/-- The no-real-or-quaternionic conclusion for any proper actual Albert decomposition. -/
theorem noRealOrQuaternionicBlock_of_noTwoFives {ι : Type*} [Fintype ι]
    (hno : NativeNoTwoFives) (d : Decomposition nativeEqualCubic ι)
    (proper : 1 < Fintype.card ι) (i : ι) :
    Module.finrank ℝ (d.piece i) ≠ 5 ∧ Module.finrank ℝ (d.piece i) ≠ 14 := by
  rcases nativeModel_closedBlocks_of_noTwoFives hno d proper with ⟨_, h2⟩ | ⟨_, j, hj, h2, _⟩
  · have h := h2 i
    omega
  · by_cases hij : i = j
    · subst i
      omega
    · have h := h2 i hij
      omega

end

end ThirteenPlanes.ClosedBlocks
