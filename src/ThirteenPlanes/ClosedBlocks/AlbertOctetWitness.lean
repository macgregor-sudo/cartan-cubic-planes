module

public import ThirteenPlanes.ClosedBlocks.CartanPieces
public import ThirteenPlanes.Graded.Incidence
public import ThirteenPlanes.Shares.OctetClosure
public import ThirteenPlanes.Shares.PairCompletions

@[expose] public section

set_option backward.privateInPublic true

/-! An actual octet with nine planes in the graded native Albert model. -/

open scoped BigOperators InnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

noncomputable section

open RoundCubics Peirce

private theorem finrank_sup_of_isOrtho {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {U W : Submodule ℝ V} (orth : U.IsOrtho W) :
    Module.finrank ℝ ↥(U ⊔ W) = Module.finrank ℝ U + Module.finrank ℝ W := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [orth.disjoint.eq_bot, finrank_bot, add_zero] at h
  exact h

/-- A literal graded Albert decomposition into one complex Cartan octet and nine closed planes. -/
theorem exists_nativeAlbert_octet_nine_planes :
    ∃ d : Decomposition nativeEqualCubic (Fin 10),
      Module.finrank ℝ (d.piece 0) = 8 ∧
      (∀ i : Fin 10, i ≠ 0 → Module.finrank ℝ (d.piece i) = 2) ∧
      ∃ I : d.piece 0 ≃ₗᵢ[ℝ] TracelessHermitian3,
        nativeEqualCubic.pullback (d.piece 0).subtype =
          Real.sqrt (1 / 6) • complexCartanCubic.pullback (W := ↥(d.piece 0)) I.toLinearMap := by
  classical
  let P := Graded.labelledDecomposition
  have hc : IsClosedPlaneSystem nativeEqualCubic P := Graded.labelledClosedPlanes
  have hbinary : ∀ k : Fin 13, k ≠ 0 → k ≠ 1 →
      planeShare nativeEqualCubic P 0 1 k = 0 ∨ planeShare nativeEqualCubic P 0 1 k = 1 := by
    intro k hk0 hk1
    exact (thirteenPlane_positive_eq_fifty_two_iff Graded.nativeRound hc).mp Graded.native_graded_support_fifty_two
      0 1 k (by decide) hk0 hk1
  obtain ⟨k, l, hkl, hk0, hk1, hl0, hl1, hh⟩ :=
    planeShare_binary_pair_completions Graded.nativeRound hc (show (0 : Fin 13) ≠ 1 from by decide) hbinary
  have hk : planeShare nativeEqualCubic P 0 1 k = 1 := (hh k hk0 hk1).mpr (Or.inl rfl)
  have hl : planeShare nativeEqualCubic P 0 1 l = 1 := (hh l hl0 hl1).mpr (Or.inr rfl)
  let S := (P.plane 0 ⊔ P.plane 1) ⊔ (P.plane k ⊔ P.plane l)
  have hS : IsClosedPiece nativeEqualCubic S := by
    have hm := mixedProductSpace_eq_of_two_unit_shares Graded.nativeRound hc (show (0 : Fin 13) ≠ 1 from by decide)
      hkl hk hl
    have hs := pairOctet_closed Graded.nativeRound (P.pairwise_orthogonal (show (0 : Fin 13) ≠ 1 from by decide))
      (hc 0) (hc 1)
    rw [hm] at hs
    exact hs (P.dimension 0) (P.dimension 1)
  have hO : (P.plane 0 ⊔ P.plane 1).IsOrtho (P.plane k ⊔ P.plane l) := by
    simp only [Submodule.isOrtho_sup_left, Submodule.isOrtho_sup_right]
    exact ⟨⟨P.pairwise_orthogonal hk0.symm, P.pairwise_orthogonal hk1.symm⟩,
      P.pairwise_orthogonal hl0.symm, P.pairwise_orthogonal hl1.symm⟩
  have hDim : Module.finrank ℝ S = 8 := by
    dsimp only [S]
    rw [finrank_sup_of_isOrtho hO, finrank_sup_of_isOrtho (P.pairwise_orthogonal (show (0 : Fin 13) ≠ 1 from by decide)),
      finrank_sup_of_isOrtho (P.pairwise_orthogonal hkl), P.dimension, P.dimension, P.dimension, P.dimension]
  let R : Finset (Fin 13) := {0, 1, k, l}
  let D := {i : Fin 13 // i ∉ R}
  have hR : R.card = 4 := by
    simp [R, Finset.card_insert_of_notMem, show (0 : Fin 13) ≠ 1 by decide,
      hkl, hk0.symm, hk1.symm, hl0.symm, hl1.symm]
  have hdcard : Fintype.card D = 9 := by
    change Fintype.card {i : Fin 13 // i ∉ R} = 9
    have h := Fintype.card_subtype_compl (p := fun i : Fin 13 => i ∈ R)
    rw [Fintype.card_fin] at h
    simpa [Fintype.card_coe, hR] using h
  let X : Option D → Submodule ℝ NativeTraceless := Option.elim' S (fun i : D => P.plane i.val)
  have hxo : Pairwise fun i j : Option D => (X i).IsOrtho (X j) := by
    rintro (_ | i) (_ | j) hij
    · exact (hij rfl).elim
    · have hn := j.property
      have hj (a : Fin 13) (ha : a ∈ R) : a ≠ j.val := fun e => hn (e ▸ ha)
      have hj0 := hj 0 (by simp [R])
      have hj1 := hj 1 (by simp [R])
      have hjk := hj k (by simp [R])
      have hjl := hj l (by simp [R])
      change S.IsOrtho (P.plane j.val)
      simp only [S, Submodule.isOrtho_sup_left]
      exact ⟨⟨P.pairwise_orthogonal hj0, P.pairwise_orthogonal hj1⟩,
        P.pairwise_orthogonal hjk, P.pairwise_orthogonal hjl⟩
    · have hn := i.property
      have hi (a : Fin 13) (ha : a ∈ R) : i.val ≠ a := fun e => hn (e.symm ▸ ha)
      change (P.plane i.val).IsOrtho S
      simp only [S, Submodule.isOrtho_sup_right]
      exact ⟨⟨P.pairwise_orthogonal (hi 0 (by simp [R])), P.pairwise_orthogonal (hi 1 (by simp [R]))⟩,
        P.pairwise_orthogonal (hi k (by simp [R])), P.pairwise_orthogonal (hi l (by simp [R]))⟩
    · exact P.pairwise_orthogonal (fun e => hij (congrArg some (Subtype.ext e)))
  have hxe : (⨆ i, X i) = ⊤ := by
    apply le_antisymm le_top
    rw [← P.exhaustive]
    refine iSup_le fun i => ?_
    by_cases hi : i ∈ R
    · apply le_trans _ (le_iSup X none)
      change P.plane i ≤ S
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_left.trans le_sup_right
      · exact le_sup_right.trans le_sup_right
    · exact le_iSup X (some ⟨i, hi⟩)
  have hxc (i : Option D) : IsClosedPiece nativeEqualCubic (X i) := by
    cases i with
    | none => exact hS
    | some i => exact hc i.val
  have hxn (i : Option D) : X i ≠ ⊥ := by
    cases i with
    | none => exact fun hz => by change S = ⊥ at hz; rw [hz, finrank_bot] at hDim; omega
    | some i =>
      intro hz
      have hh := P.dimension i.val
      change P.plane i.val = ⊥ at hz
      rw [hz, finrank_bot] at hh
      omega
  have hcard : Fintype.card (Option D) = 10 := by rw [Fintype.card_option, hdcard]
  let f := Fintype.equivFinOfCardEq hcard
  let e : Fin 10 ≃ Option D := ((Equiv.swap 0 (f none)).trans f.symm)
  have he : e 0 = none := by simp [e, Equiv.swap_apply_left]
  let d : Decomposition nativeEqualCubic (Fin 10) :=
    ⟨fun i => X (e i), fun i => hxn _, fun _ _ hij => hxo (e.injective.ne hij), by
      rw [e.iSup_comp, hxe], fun i => hxc _⟩
  have hdim : Module.finrank ℝ (d.piece 0) = 8 := by change Module.finrank ℝ (X (e 0)) = _; rw [he]; exact hDim
  have ht : nativeEqualCubic.TraceFree := traceFree_of_isClosedPlaneSystem Graded.nativeRound hc
  refine ⟨d, hdim, ?_, d.octet_isometry Graded.nativeRound ht 0 hdim⟩
  intro i hi
  have hne : e i ≠ none := fun h => hi (e.injective (h.trans he.symm))
  change Module.finrank ℝ (X (e i)) = 2
  cases hei : e i with
  | none => exact (hne hei).elim
  | some j => exact P.dimension j.val

end

end ThirteenPlanes.ClosedBlocks
