module

public import ThirteenPlanes.Shares.OctetClosure
public import ThirteenPlanes.Shares.ProjectiveNormalForm

@[expose] public section

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {c : ℝ} {h : SymmetricCubic V}

/-- Binary shares are equivalent to each pair lying in an actual closed quartet.
The forward implication uses the slice-based proof of genuine pair-octet closure. -/
theorem planeShare_binary_iff_quartet_cover {m : ℕ} {system : PlaneDecomposition V (Fin m)}
    (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (∀ i j k : Fin m, i ≠ j → k ≠ i → k ≠ j →
      planeShare h system i j k = 0 ∨ planeShare h system i j k = 1) ↔
    ∀ i j : Fin m, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B := by
  constructor
  · intro binary
    apply planeQuartet_cover_of_binary_shares round closed ?_ binary
    intro i j hij
    exact pairOctet_closed round (system.pairwise_orthogonal hij) (closed i) (closed j)
      (system.dimension i) (system.dimension j)
  · intro cover i j k hij hki hkj
    rw [planeShare_binary_of_quartet_cover round closed cover hij hki hkj]
    split <;> simp

/-- The thirteen-plane support and incidence theorem, with its count, four equivalences, unique quartet through each pair,
and the standard projective incidence and 0/1 collinearity formula. -/
theorem thirteenPlane_shareSupport_and_incidence {system : PlaneDecomposition V (Fin 13)}
    (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    let sparse := (positivePlaneTriples h system).card = 52
    let binary := ∀ i j k : Fin 13, i ≠ j → k ≠ i → k ≠ j →
      planeShare h system i j k = 0 ∨ planeShare h system i j k = 1
    let quartets := ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B
    let projective := ∃ P : Configuration.ProjectivePlane (Fin 13) (PlaneQuartetLine h system),
      @Configuration.ProjectivePlane.order (Fin 13) (PlaneQuartetLine h system) _ P = 3
    (Fintype.card (IncreasingPlaneTriple 13) = 286 ∧
      (∑ t : IncreasingPlaneTriple 13, unorderedPlaneShare h system t) = 52 ∧
      52 ≤ (positivePlaneTriples h system).card) ∧
    (sparse ↔ binary) ∧ (binary ↔ quartets) ∧ (quartets ↔ projective) ∧
    (sparse →
      (∀ i j : Fin 13, i ≠ j → ∃! B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B) ∧
      ∃ p : PGThreePoint ≃ Fin 13, ∃ L : PGThreeLine ≃ PlaneQuartetLine h system,
        (∀ x B, p x ∈ L B ↔ pgThreeIncidence x B) ∧
        (∀ x y z : PGThreePoint, x ≠ y → z ≠ x → z ≠ y →
          planeShare h system (p x) (p y) (p z) =
            (if ∃ B : PGThreeLine, pgThreeIncidence x B ∧ pgThreeIncidence y B ∧ pgThreeIncidence z B
              then 1 else 0))) := by
  dsimp only
  have hab := thirteenPlane_positive_eq_fifty_two_iff round closed
  have hbc := planeShare_binary_iff_quartet_cover round closed
  have hcd := thirteenPlane_quartet_cover_iff_projective round closed
  refine ⟨thirteenPlane_share_counts round closed, hab, hbc, hcd, fun sparse => ?_⟩
  have cover := hbc.mp (hab.mp sparse)
  obtain ⟨p, L, hinc⟩ := thirteenPlane_quartets_isomorphic_pgThree round closed cover
  exact ⟨(thirteenPlane_quartet_incidence round closed cover).1, p, L, hinc, fun _ _ _ =>
    thirteenPlane_share_eq_pgThree_collinearity round closed p L hinc⟩

end
end ThirteenPlanes.RoundCubics
