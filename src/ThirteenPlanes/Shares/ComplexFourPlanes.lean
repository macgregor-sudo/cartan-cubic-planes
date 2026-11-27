module

public import ThirteenPlanes.Shares.PairCompletions
public import ThirteenPlanes.Shares.ThreePlanes
public import ThirteenPlanes.PeirceDimensions
public import ThirteenPlanes.FourPlanesDecomposition

@[expose] public section

namespace ThirteenPlanes.RoundCubics

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The four-plane theorem (ii) for an arbitrary complete system of closed planes in
the actual traceless complex Hermitian 3-by-3 model. -/
theorem complex_closedPlaneSystem_four
    (system : PlaneDecomposition TracelessHermitian3 ι)
    (closed : IsClosedPlaneSystem matrixEqualCubic system) :
    Fintype.card ι = 4 ∧
    (∀ i j k : ι, i ≠ j → k ≠ i → k ≠ j → planeShare matrixEqualCubic system i j k = 1) ∧
    (∀ i j k l : ι, i ≠ j → k ≠ i → k ≠ j → l ≠ i → l ≠ j → k ≠ l →
      mixedProductSpace matrixEqualCubic (system.plane i) (system.plane j) =
        system.plane k ⊔ system.plane l) := by
  classical
  have dim : Module.finrank ℝ TracelessHermitian3 = 8 := by
    simpa using Peirce.finrank_eq_twice_card fourPlaneDecomposition
  have hdim := Peirce.finrank_eq_twice_card system
  have hcard : Fintype.card ι = 4 := by omega
  have round : IsRound matrixEqualCubic (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [matrixEqualCubic_squareMap, TracelessHermitian3.square_norm_sq]
    ring
  let r : ι ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let Q : PlaneDecomposition TracelessHermitian3 (Fin 4) :=
    { plane := fun k => system.plane (r.symm k)
      dimension := fun k => system.dimension (r.symm k)
      pairwise_orthogonal := fun _ _ hk => system.pairwise_orthogonal (r.symm.injective.ne hk)
      exhaustive := (r.symm.iSup_comp (g := system.plane)).trans system.exhaustive }
  have hQ : IsClosedPlaneSystem matrixEqualCubic Q := fun k => closed (r.symm k)
  have hp (i : ι) : Q.plane (r i) = system.plane i := by
    change system.plane (r.symm (r i)) = _
    rw [r.symm_apply_apply]
  have hrew (i j k : ι) : planeShare matrixEqualCubic Q (r i) (r j) (r k) =
      planeShare matrixEqualCubic system i j k := by
    rw [planeShare_eq_shareOfThreePlanes, planeShare_eq_shareOfThreePlanes, hp, hp, hp]
  have result (i j k l : ι) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
      (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l) :=
    fourPlane_unit_shares round hQ (r.injective.ne hij) (r.injective.ne hki)
      (r.injective.ne hkj) (r.injective.ne hli) (r.injective.ne hlj) (r.injective.ne hkl)
  refine ⟨hcard, ?_, ?_⟩
  · intro i j k hij hki hkj
    have hs : ({i, j, k} : Finset ι).card < (Finset.univ : Finset ι).card := by
      rw [Finset.card_univ, hcard]
      simp [hij, hki.symm, hkj.symm]
    obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
    have hli : l ≠ i := fun he => hl (he ▸ by simp)
    have hlj : l ≠ j := fun he => hl (he ▸ by simp)
    have hlk : l ≠ k := fun he => hl (he ▸ by simp)
    rw [← hrew]
    exact (result i j k l hij hki hkj hli hlj hlk.symm).1
  · intro i j k l hij hki hkj hli hlj hkl
    have hm := (result i j k l hij hki hkj hli hlj hkl).2.2
    rwa [hp, hp, hp, hp] at hm

end
end ThirteenPlanes.RoundCubics
