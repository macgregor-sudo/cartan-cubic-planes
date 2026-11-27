module

public import ThirteenPlanes.PlaneShares

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m : ℕ} {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin m)}

private abbrev otherPlanes {m : ℕ} (i j : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)

private theorem otherPlanes_card {i j : Fin m} (hij : i ≠ j) : (otherPlanes i j).card = m - 2 := by
  have hs : otherPlanes i j = (Finset.univ.erase i).erase j := by
    ext k
    simp [and_comm]
  rw [hs, Finset.card_erase_of_mem (by simpa using hij.symm), Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp
  omega

/-- A proper orthogonal decomposition of a round cubic has at least four closed planes.
This is the four-plane theorem (i). -/
theorem round_planeSystem_at_least_four (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    (proper : 2 ≤ m) : 4 ≤ m := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro he
    have hval := congrArg Fin.val he
    norm_num [i, j] at hval
  have hc : (2 : ℝ) ≤ (otherPlanes i j).card := by
    calc
      _ = ∑ k ∈ otherPlanes i j, planeShare h system i j k := (planeShare_pair_sum round closed hij).symm
      _ ≤ ∑ _k ∈ otherPlanes i j, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => (planeShare_bounds h system i j k).1.2
      _ = _ := by simp
  have htwo : 2 ≤ (otherPlanes i j).card := by exact_mod_cast hc
  rw [otherPlanes_card hij] at htwo
  omega

/-- At saturation, each pair has precisely two distinct positive third planes. Both shares are one. -/
theorem planeShare_binary_pair_completions (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    {i j : Fin m} (hij : i ≠ j)
    (binary : ∀ k, k ≠ i → k ≠ j → planeShare h system i j k = 0 ∨ planeShare h system i j k = 1) :
    ∃ k l, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
      ∀ t, t ≠ i → t ≠ j → (planeShare h system i j t = 1 ↔ t = k ∨ t = l) := by
  let C := (otherPlanes i j).filter (fun k => planeShare h system i j k = 1)
  have hsum : (∑ k ∈ C, (1 : ℝ)) = 2 := by
    change (∑ k ∈ (otherPlanes i j).filter (fun k => planeShare h system i j k = 1), (1 : ℝ)) = 2
    rw [Finset.sum_filter, ← planeShare_pair_sum round closed hij]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hki, hkj⟩ := (Finset.mem_filter.mp hk).2
    rcases binary k hki hkj with hk | hk <;> simp [hk]
  have hcard : C.card = 2 := by
    have hc : (C.card : ℝ) = 2 := by simpa using hsum
    exact_mod_cast hc
  obtain ⟨k, l, hkl, hC⟩ := Finset.card_eq_two.mp hcard
  have hk : k ∈ C := by simp [hC]
  have hl : l ∈ C := by simp [hC]
  have hkmem := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  have hlmem := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
  refine ⟨k, l, hkl, hkmem.1, hkmem.2, hlmem.1, hlmem.2, fun t hti htj => ?_⟩
  have ht : t ∈ otherPlanes i j := by simp [hti, htj]
  have hm : t ∈ C ↔ planeShare h system i j t = 1 := by simp [C, ht]
  rw [← hm, hC]
  simp

theorem mixedProductSpace_eq_of_two_unit_shares (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l)
    (hk : planeShare h system i j k = 1) (hl : planeShare h system i j l = 1) :
    mixedProductSpace h (system.plane i) (system.plane j) = system.plane k ⊔ system.plane l := by
  have hk' := (planeShare_bounds h system i j k).2.1.mp hk
  have hl' := (planeShare_bounds h system i j l).2.1.mp hl
  symm
  apply Submodule.eq_of_le_of_finrank_le (sup_le hk' hl')
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (system.plane k) (system.plane l)
  rw [(system.pairwise_orthogonal hkl).disjoint.eq_bot, finrank_bot, add_zero, system.dimension,
    system.dimension] at hdim
  rw [hdim, mixedProductSpace_finrank round (system.pairwise_orthogonal hij) (closed i) (closed j)
    (system.dimension i) (system.dimension j)]

/-- In every four-plane system, all shares are one and every pair has the other two planes
as its product space. These are the share and product-space clauses of the four-plane theorem (ii). -/
theorem fourPlane_unit_shares {system : PlaneDecomposition V (Fin 4)}
    (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    {i j k l : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l) :
    planeShare h system i j k = 1 ∧ planeShare h system i j l = 1 ∧
      mixedProductSpace h (system.plane i) (system.plane j) = system.plane k ⊔ system.plane l := by
  have hs : otherPlanes i j = {k, l} := by
    have hf : ({k, l} : Finset (Fin 4)) ⊆ otherPlanes i j := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · simp [hki, hkj]
      · obtain rfl : t = l := Finset.mem_singleton.mp ht
        simp [hli, hlj]
    symm
    apply Finset.eq_of_subset_of_card_le hf
    rw [otherPlanes_card hij]
    simp [hkl]
  have hp := planeShare_pair_sum round closed hij
  change (∑ t ∈ otherPlanes i j, _) = 2 at hp
  rw [hs, Finset.sum_pair hkl] at hp
  have hk : planeShare h system i j k = 1 := by
    linarith [(planeShare_bounds h system i j k).1.2, (planeShare_bounds h system i j l).1.2]
  have hl : planeShare h system i j l = 1 := by linarith
  exact ⟨hk, hl, mixedProductSpace_eq_of_two_unit_shares round closed hij hkl hk hl⟩

end
end ThirteenPlanes.RoundCubics
