module

public import ThirteenPlanes.ClosedBlocks.AlbertOctetWitness
public import ThirteenPlanes.RoundContractions

@[expose] public section

/-! Arithmetic and metric transport for the closed-block classification. -/

open scoped BigOperators InnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce

noncomputable section

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {h : SymmetricCubic V} {g : SymmetricCubic W} {c : ℝ} {ι : Type*}

/-- A proper split can be transported without changing its indexing or block dimensions. -/
def Decomposition.mapIsometry (d : Decomposition h ι) (I : V ≃ₗᵢ[ℝ] W)
    (hI : h = g.pullback I.toLinearMap) : Decomposition g ι where
  piece i := (d.piece i).map I.toLinearMap
  nonzero i := by
    intro hz
    apply d.nonzero i
    have hm := congrArg (Submodule.comap I.toLinearMap) hz
    rwa [Submodule.comap_map_eq_of_injective I.injective, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr I.injective] at hm
  orthogonal _ _ hij := isOrtho_map_isometry I (d.orthogonal hij)
  exhaustive := by
    rw [← Submodule.map_iSup, d.exhaustive, Submodule.map_top,
      LinearMap.range_eq_top.mpr I.surjective]
  closed i := isClosedPiece_map_isometry I hI (d.closed i)

omit [FiniteDimensional ℝ W] in
theorem Decomposition.mapIsometry_finrank (d : Decomposition h ι) (I : V ≃ₗᵢ[ℝ] W)
    (hI : h = g.pullback I.toLinearMap) (i : ι) :
    Module.finrank ℝ ((d.mapIsometry I hI).piece i) = Module.finrank ℝ (d.piece i) :=
  (mapBlockIsometry I (d.piece i)).toLinearEquiv.finrank_eq.symm

/-- Multiplication of the ambient cubic by a nonzero scalar preserves every member of the split. -/
def Decomposition.smul (d : Decomposition h ι) {s : ℝ} (hs : s ≠ 0) : Decomposition (s • h) ι :=
  ⟨d.piece, d.nonzero, d.orthogonal, d.exhaustive,
    fun i => (isClosedPiece_smul_iff hs (d.piece i)).mpr (d.closed i)⟩

/-- The four actual matrix planes give an exhaustive decomposition of the complex trace cubic. -/
theorem exists_complex_four_plane_decomposition :
    ∃ d : Decomposition complexCartanCubic (Fin 4),
      ∀ i, Module.finrank ℝ (d.piece i) = 2 := by
  let P := fourPlaneDecomposition
  have hC : ∀ i, IsClosedPiece complexCartanCubic (P.plane i) := by
    intro i
    rw [complexCartanCubic, isClosedPiece_smul_iff (by positivity), ← interactionCubic_fourPlanePair_one]
    intro x y hx hy
    have hxy : (interactionCubic fourPlanePair 1).L x y ∈ (P.plane i)ᗮᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      exact fourPlaneData.repeatedPlane i ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    rwa [Submodule.orthogonal_orthogonal] at hxy
  exact ⟨⟨P.plane, fun i => by
    intro hz
    have hd := P.dimension i
    rw [hz, finrank_bot] at hd
    omega, P.pairwise_orthogonal, P.exhaustive, hC⟩, P.dimension⟩

/-- The thirteen explicit graded planes are a decomposition of the native Albert trace cubic. -/
theorem exists_nativeAlbert_thirteen_plane_decomposition :
    ∃ d : Decomposition nativeEqualCubic (Fin 13),
      ∀ i, Module.finrank ℝ (d.piece i) = 2 := by
  let P := Graded.labelledDecomposition
  exact ⟨⟨P.plane, fun i => by
    intro hz
    have hd := P.dimension i
    rw [hz, finrank_bot] at hd
    omega, P.pairwise_orthogonal, P.exhaustive, Graded.labelledClosedPlanes⟩, P.dimension⟩

section Finite

variable [Fintype ι]

/-- If a block differs from two dimensions and all the others are planes, it
contributes its dimension in addition to two per remaining index. -/
theorem Decomposition.finrank_eq_piece_add_twice_card_sub_one (d : Decomposition h ι)
    (i : ι) (hothers : ∀ j, j ≠ i → Module.finrank ℝ (d.piece j) = 2) :
    Module.finrank ℝ V = Module.finrank ℝ (d.piece i) + 2 * (Fintype.card ι - 1) := by
  classical
  rw [d.finrank_eq_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hsum : ∑ j ∈ Finset.univ.erase i, Module.finrank ℝ (d.piece j) =
      2 * (Fintype.card ι - 1) := by
    rw [show (∑ j ∈ Finset.univ.erase i, Module.finrank ℝ (d.piece j)) =
        ∑ _j ∈ Finset.univ.erase i, 2 from Finset.sum_congr rfl
          (fun j hj => hothers j (Finset.ne_of_mem_erase hj)), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, nsmul_eq_mul, Nat.mul_comm]
    rfl
  rw [hsum, add_comm]

/-- A decomposition containing an octet with only planes orthogonal to it has nine other pieces. -/
theorem Decomposition.octet_has_nine_other_planes (d : Decomposition h ι)
    (round : IsRound h c) (tf : h.TraceFree) (hV : Module.finrank ℝ V = 26)
    (i : ι) (hi : Module.finrank ℝ (d.piece i) = 8)
    (octetBound : ∀ S : Submodule ℝ V, IsClosedPiece h S → (d.piece i).IsOrtho S →
      Module.finrank ℝ S ≤ 2) :
    Fintype.card ι = 10 ∧ ∀ j, j ≠ i → Module.finrank ℝ (d.piece j) = 2 := by
  have hothers (j : ι) (hj : j ≠ i) : Module.finrank ℝ (d.piece j) = 2 := by
    have hd := d.piece_dim_cases round tf j
    have hb := octetBound (d.piece j) (d.closed j) (d.orthogonal hj.symm)
    omega
  have hd := d.finrank_eq_piece_add_twice_card_sub_one i hothers
  exact ⟨by omega, hothers⟩

/-- The ambient and individual Cartan dimensions together imply the three
harmonic patterns once the two orthogonal exclusions in dimension 26 are known. -/
theorem classifyHarmonicRoundDecompositions_of_orthogonal_exclusions (d : Decomposition h ι)
    (round : IsRound h c) (tf : h.TraceFree) (proper : 1 < Fintype.card ι)
    (octetBound : Module.finrank ℝ V = 26 → ∀ U S : Submodule ℝ V,
      IsClosedPiece h U → IsClosedPiece h S → U.IsOrtho S →
      (h.pullback U.subtype).TraceFree →
      Module.finrank ℝ U = 8 → Module.finrank ℝ S ≤ 2)
    (fiveBound : Module.finrank ℝ V = 26 → ∀ U S : Submodule ℝ V,
      IsClosedPiece h U → IsClosedPiece h S → U.IsOrtho S →
      (h.pullback U.subtype).TraceFree → (h.pullback S.subtype).TraceFree →
      Module.finrank ℝ U = 5 → Module.finrank ℝ S ≠ 5) :
    (Module.finrank ℝ V = 8 ∧ Fintype.card ι = 4 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∨
      (Module.finrank ℝ V = 26 ∧
        ((Fintype.card ι = 13 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∨
         (Fintype.card ι = 10 ∧ ∃ i, Module.finrank ℝ (d.piece i) = 8 ∧
           (∀ j, j ≠ i → Module.finrank ℝ (d.piece j) = 2) ∧
           ∃ I : d.piece i ≃ₗᵢ[ℝ] TracelessHermitian3,
             h.pullback (d.piece i).subtype =
               Real.sqrt c • complexCartanCubic.pullback (W := ↥(d.piece i)) I.toLinearMap))) := by
  classical
  rcases harmonic_decomposition_dim_eight_or_twentySix d round tf proper with hlow | ⟨hV, hcases⟩
  · exact Or.inl hlow
  refine Or.inr ⟨hV, ?_⟩
  have ht := (closedPieces_traceFree_iff d.orthogonal d.exhaustive d.closed).mp tf
  by_cases h8 : ∃ i, Module.finrank ℝ (d.piece i) = 8
  · obtain ⟨i, hi⟩ := h8
    have hs := d.octet_has_nine_other_planes round tf hV i hi
      (fun S hS ho => octetBound hV (d.piece i) S (d.closed i) hS ho (ht i) hi)
    exact Or.inr ⟨hs.1, i, hi, hs.2, d.octet_isometry round tf i hi⟩
  have hno5 (i : ι) : Module.finrank ℝ (d.piece i) ≠ 5 := by
    intro hi
    have hothers (j : ι) (hj : j ≠ i) : Module.finrank ℝ (d.piece j) = 2 := by
      have hj5 := fiveBound hV (d.piece i) (d.piece j) (d.closed i) (d.closed j)
        (d.orthogonal hj.symm) (ht i) (ht j) hi
      rcases hcases j with h | h | h
      · exact h
      · exact (hj5 h).elim
      · exact (h8 ⟨j, h⟩).elim
    have hsum := d.finrank_eq_piece_add_twice_card_sub_one i hothers
    omega
  have htwo (i : ι) : Module.finrank ℝ (d.piece i) = 2 :=
    ((hcases i).resolve_right (fun hs => hs.elim (hno5 i) (fun he => h8 ⟨i, he⟩)))
  have hs := d.finrank_eq_sum
  rw [show (∑ i, Module.finrank ℝ (d.piece i)) = ∑ _i : ι, 2 from Finset.sum_congr rfl
    (fun i _ => htwo i)] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  change Module.finrank ℝ V = Fintype.card ι * 2 at hs
  exact Or.inl ⟨by omega, htwo⟩

end Finite

end

end ThirteenPlanes.ClosedBlocks
