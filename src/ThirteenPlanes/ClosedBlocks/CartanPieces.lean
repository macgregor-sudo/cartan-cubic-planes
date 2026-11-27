module

public import ThirteenPlanes.ClosedBlocks.Dimensions

@[expose] public section

/-! Actual metric Cartan comparisons for closed harmonic pieces. -/

open scoped InnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

noncomputable section

open Peirce RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : SymmetricCubic V} {c : ℝ}

/-- An eight-dimensional harmonic round cubic is the positive scaled complex trace cubic. -/
theorem harmonic_round_eight_cartan (round : IsRound h c) (tf : h.TraceFree)
    (dim : Module.finrank ℝ V = 8) :
    ∃ I : V ≃ₗᵢ[ℝ] TracelessHermitian3, h = Real.sqrt c • complexCartanCubic.pullback I.toLinearMap := by
  let g := unitNormalize h c
  have gr : IsRound g 1 := unitNormalize_isRound round
  have gt : g.TraceFree := unitNormalize_traceFree tf
  have hv : 0 < Module.finrank ℝ V := by omega
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hv
  obtain ⟨a, ha⟩ := exists_unitIdempotent g gr
  have htrace := gt a
  obtain ⟨_, hdim, _⟩ := finrank_exact_of_trace_zero gr ha htrace
  have hm : 0 < Module.finrank ℝ (minusSpace g a) := by omega
  let : Nontrivial ↥(minusSpace g a) := Module.nontrivial_of_finrank_pos hm
  obtain ⟨b, hb⟩ := exists_norm_eq ↥(minusSpace g a) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨I, _, _, hI⟩ := markedRoundCubic_complex gr ha hb htrace dim
  exact ⟨I, (eq_smul_unitNormalize round).trans (congrArg (Real.sqrt c • ·) hI)⟩

/-- The actual restriction to an eight-dimensional block is a complex Cartan octet. -/
theorem Decomposition.octet_isometry {ι : Type*} [Fintype ι] (d : Decomposition h ι)
    (round : IsRound h c) (tf : h.TraceFree) (i : ι) (hd : Module.finrank ℝ (d.piece i) = 8) :
    ∃ I : d.piece i ≃ₗᵢ[ℝ] TracelessHermitian3,
      h.pullback (d.piece i).subtype = Real.sqrt c • complexCartanCubic.pullback I.toLinearMap :=
  harmonic_round_eight_cartan (closedSubspace_restriction_isRound round (d.closed i))
    ((closedPieces_traceFree_iff d.orthogonal d.exhaustive d.closed).mp tf i) hd


/-- A harmonic round five-space is the actual real Cartan cubic at the ambient strength. -/
theorem harmonic_round_five_cartan (round : IsRound h c) (tf : h.TraceFree)
    (dim : Module.finrank ℝ V = 5) :
    ∃ I : V ≃ₗᵢ[ℝ] RealTracelessSymmetric3,
      h = Real.sqrt c • realCartanCubic.pullback I.toLinearMap := by
  let g := unitNormalize h c
  have gr : IsRound g 1 := unitNormalize_isRound round
  have gt : g.TraceFree := unitNormalize_traceFree tf
  have hv : 0 < Module.finrank ℝ V := by omega
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hv
  obtain ⟨a, ha⟩ := exists_unitIdempotent g gr
  have htrace := gt a
  obtain ⟨_, hdim, _⟩ := finrank_exact_of_trace_zero gr ha htrace
  have hm : 0 < Module.finrank ℝ (minusSpace g a) := by omega
  let : Nontrivial ↥(minusSpace g a) := Module.nontrivial_of_finrank_pos hm
  obtain ⟨b, hb⟩ := exists_norm_eq ↥(minusSpace g a) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨I, _, _, hI⟩ := markedRoundCubic_real gr ha hb htrace dim
  exact ⟨I, (eq_smul_unitNormalize round).trans (congrArg (Real.sqrt c • ·) hI)⟩

/-- A harmonic round twenty-six-space is the actual Albert trace cubic at its strength. -/
theorem harmonic_round_twentySix_albert (round : IsRound h c) (tf : h.TraceFree)
    (dim : Module.finrank ℝ V = 26) :
    ∃ I : V ≃ₗᵢ[ℝ] NativeTraceless,
      h = (Real.sqrt c * Real.sqrt 6) • nativeEqualCubic.pullback I.toLinearMap := by
  let g := unitNormalize h c
  have gr : IsRound g 1 := unitNormalize_isRound round
  have gt : g.TraceFree := unitNormalize_traceFree tf
  have hv : 0 < Module.finrank ℝ V := by omega
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hv
  obtain ⟨a, ha⟩ := exists_unitIdempotent g gr
  have htrace := gt a
  obtain ⟨_, hdim, _⟩ := finrank_exact_of_trace_zero gr ha htrace
  have hm : 0 < Module.finrank ℝ (minusSpace g a) := by omega
  let : Nontrivial ↥(minusSpace g a) := Module.nontrivial_of_finrank_pos hm
  obtain ⟨b, hb⟩ := exists_norm_eq ↥(minusSpace g a) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨I, _, _, hI⟩ := markedRoundCubic_native gr ha hb htrace dim
  have hh := eq_smul_unitNormalize round
  change h = Real.sqrt c • g at hh
  rw [hh, hI, nativeCartanCubic, pullback_smul_cubic, smul_smul]
  exact ⟨I, rfl⟩

end

end ThirteenPlanes.ClosedBlocks
