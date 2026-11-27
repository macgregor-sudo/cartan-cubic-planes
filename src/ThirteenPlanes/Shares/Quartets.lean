module

public import ThirteenPlanes.Shares.PairCompletions
public import ThirteenPlanes.Shares.Support

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m : ℕ} {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin m)}

/-- A quartet in the manuscript is a set of four planes whose sum is closed. -/
def IsPlaneQuartet (h : SymmetricCubic V) (system : PlaneDecomposition V (Fin m))
    (B : Finset (Fin m)) : Prop :=
  B.card = 4 ∧ IsClosedPiece h (⨆ i ∈ B, system.plane i)

private theorem finrank_plane_sup {i j : Fin m} (hij : i ≠ j) :
    Module.finrank ℝ ↥(system.plane i ⊔ system.plane j) = 4 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (system.plane i) (system.plane j)
  rw [(system.pairwise_orthogonal hij).disjoint.eq_bot, finrank_bot, add_zero,
    system.dimension, system.dimension] at hdim
  exact hdim

omit [FiniteDimensional ℝ V] in
private theorem iSup_four (i j k l : Fin m) :
    (⨆ t ∈ ({i, j, k, l} : Finset (Fin m)), system.plane t) =
      (system.plane i ⊔ system.plane j) ⊔ (system.plane k ⊔ system.plane l) := by
  apply le_antisymm
  · refine iSup_le fun t => iSup_le fun ht => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    all_goals exact le_iSup_of_le _ (le_iSup_of_le (by simp) le_rfl)

private theorem quartet_eq_pair_and_complements {B : Finset (Fin m)} (hB : B.card = 4)
    {i j : Fin m} (hij : i ≠ j) (hi : i ∈ B) (hj : j ∈ B) :
    ∃ k l, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ B = {i, j, k, l} := by
  let C := (B.erase i).erase j
  have hC : C.card = 2 := by
    dsimp only [C]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, hj⟩),
      Finset.card_erase_of_mem hi, hB]
  obtain ⟨k, l, hkl, h₂⟩ := Finset.card_eq_two.mp hC
  have hk : k ∈ C := by simp [h₂]
  have hl : l ∈ C := by simp [h₂]
  have hk' := Finset.mem_erase.mp hk
  have hl' := Finset.mem_erase.mp hl
  have hk'' := Finset.mem_erase.mp hk'.2
  have hl'' := Finset.mem_erase.mp hl'.2
  refine ⟨k, l, hkl, hk''.1, hk'.1, hl''.1, hl'.1, ?_⟩
  ext t
  by_cases hti : t = i
  · subst t; simp [hi]
  by_cases htj : t = j
  · subst t; simp [hj]
  · have ht : t ∈ C ↔ t ∈ B := by simp [C, hti, htj]
    simp [hti, htj, ← ht, h₂]

private theorem mixed_space_of_closed_four (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (hO : IsClosedPiece h ((system.plane i ⊔ system.plane j) ⊔ (system.plane k ⊔ system.plane l))) :
    mixedProductSpace h (system.plane i) (system.plane j) = system.plane k ⊔ system.plane l := by
  let A := system.plane i ⊔ system.plane j
  let B := system.plane k ⊔ system.plane l
  let W := mixedProductSpace h (system.plane i) (system.plane j)
  have hW : W ≤ A ⊔ B := by
    dsimp only [W]
    rw [mixedProductSpace_eq_span]
    apply Submodule.map₂_le.mpr
    intro x hx y hy
    have hi : system.plane i ≤ A ⊔ B := le_sup_left.trans le_sup_left
    have hj : system.plane j ≤ A ⊔ B := le_sup_right.trans le_sup_left
    exact hO (hi hx) (hj hy)
  have hWo : W ≤ Aᗮ :=
    mixedProductSpace_le_orthogonal round (system.pairwise_orthogonal hij) (closed i) (closed j)
  have hBo : B ≤ Aᗮ := by
    exact Submodule.isOrtho_iff_le.mp (Submodule.isOrtho_sup_left.mpr
      ⟨Submodule.isOrtho_sup_right.mpr ⟨system.pairwise_orthogonal hki, system.pairwise_orthogonal hkj⟩,
       Submodule.isOrtho_sup_right.mpr ⟨system.pairwise_orthogonal hli, system.pairwise_orthogonal hlj⟩⟩)
  have hWB : W ≤ B := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hW hx)
    have hab : a + b ∈ Aᗮ := hWo hx
    have ha' : a ∈ Aᗮ := by simpa using Aᗮ.sub_mem hab (hBo hb)
    have hzero : a = 0 := by
      have hbot : a ∈ A ⊓ Aᗮ := ⟨ha, ha'⟩
      rwa [A.orthogonal_disjoint.eq_bot, Submodule.mem_bot] at hbot
    simpa [hzero] using hb
  apply Submodule.eq_of_le_of_finrank_le hWB
  rw [show Module.finrank ℝ B = 4 from finrank_plane_sup (system := system) hkl]
  rw [show Module.finrank ℝ W = 4 from
    mixedProductSpace_finrank round (system.pairwise_orthogonal hij) (closed i) (closed j)
      (system.dimension i) (system.dimension j)]

/-- Within any actual closed quartet, each fixed pair shares one with exactly the other two planes. -/
theorem planeShare_eq_one_iff_mem_quartet (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    {B : Finset (Fin m)} (quartet : IsPlaneQuartet h system B)
    {i j t : Fin m} (hij : i ≠ j) (hi : i ∈ B) (hj : j ∈ B) (hti : t ≠ i) (htj : t ≠ j) :
    planeShare h system i j t = (if t ∈ B then 1 else 0) := by
  obtain ⟨k, l, hkl, hki, hkj, hli, hlj, rfl⟩ := quartet_eq_pair_and_complements quartet.1 hij hi hj
  have hO := quartet.2
  rw [iSup_four] at hO
  have hW := mixed_space_of_closed_four round closed hij hkl hki hkj hli hlj hO
  by_cases htk : t = k
  · subst t
    rw [ite_eq_left (by simp)]
    exact (planeShare_bounds h system i j k).2.1.mpr (by rw [hW]; exact le_sup_left)
  by_cases htl : t = l
  · subst t
    rw [ite_eq_left (by simp)]
    exact (planeShare_bounds h system i j l).2.1.mpr (by rw [hW]; exact le_sup_right)
  rw [ite_eq_right (by simp [hti, htj, htk, htl])]
  exact (planeShare_bounds h system i j t).2.2.mpr (by
    rw [hW]
    exact Submodule.isOrtho_sup_right.mpr
      ⟨system.pairwise_orthogonal htk, system.pairwise_orthogonal htl⟩)

/-- Two actual closed quartets containing a common pair coincide. -/
theorem planeQuartet_unique_through_pair (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    {B D : Finset (Fin m)} (hB : IsPlaneQuartet h system B) (hD : IsPlaneQuartet h system D)
    {i j : Fin m} (hij : i ≠ j) (hiB : i ∈ B) (hjB : j ∈ B) (hiD : i ∈ D) (hjD : j ∈ D) :
    B = D := by
  ext t
  by_cases hti : t = i
  · subst t; simp [hiB, hiD]
  by_cases htj : t = j
  · subst t; simp [hjB, hjD]
  · have hs := (planeShare_eq_one_iff_mem_quartet round closed hB hij hiB hjB hti htj).symm.trans
      (planeShare_eq_one_iff_mem_quartet round closed hD hij hiD hjD hti htj)
    by_cases htB : t ∈ B <;> by_cases htD : t ∈ D <;> simp_all

/-- If every pair lies in a quartet, shares are binary and positive precisely on triples
contained in a quartet. This proves the thirteen-plane support and incidence theorem (ii)(c) implies (b), as well as its
collinear-triple formula under (c). -/
theorem planeShare_binary_of_quartet_cover (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    (cover : ∀ i j : Fin m, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)
    {i j t : Fin m} (hij : i ≠ j) (hti : t ≠ i) (htj : t ≠ j) :
    planeShare h system i j t =
      (if ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B ∧ t ∈ B then 1 else 0) := by
  classical
  obtain ⟨B, hB, hi, hj⟩ := cover i j hij
  rw [planeShare_eq_one_iff_mem_quartet round closed hB hij hi hj hti htj]
  have he : (∃ D, IsPlaneQuartet h system D ∧ i ∈ D ∧ j ∈ D ∧ t ∈ D) ↔ t ∈ B := by
    constructor
    · rintro ⟨D, hD, hiD, hjD, htD⟩
      rwa [← planeQuartet_unique_through_pair round closed hB hD hij hi hj hiD hjD] at htD
    · exact fun ht => ⟨B, hB, hi, hj, ht⟩
  simp only [he]

/-- A geometric closure theorem for the pair and its product space supplies the missing implication
from binary shares to genuine quartet coverage, as in the thirteen-plane support and incidence theorem (ii)(b) implies (c). -/
theorem planeQuartet_cover_of_binary_shares (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    (octet_closed : ∀ i j : Fin m, i ≠ j →
      IsClosedPiece h ((system.plane i ⊔ system.plane j) ⊔
        mixedProductSpace h (system.plane i) (system.plane j)))
    (binary : ∀ i j k : Fin m, i ≠ j → k ≠ i → k ≠ j →
      planeShare h system i j k = 0 ∨ planeShare h system i j k = 1) :
    ∀ i j : Fin m, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B := by
  intro i j hij
  obtain ⟨k, l, hkl, hki, hkj, hli, hlj, hk⟩ := planeShare_binary_pair_completions round closed hij (binary i j · hij)
  have hW := mixedProductSpace_eq_of_two_unit_shares round closed hij hkl
    ((hk k hki hkj).mpr (Or.inl rfl)) ((hk l hli hlj).mpr (Or.inr rfl))
  have hO := octet_closed i j hij
  rw [hW] at hO
  refine ⟨{i, j, k, l}, ⟨?_, ?_⟩, by simp, by simp⟩
  · simp [hij, hki.symm, hli.symm, hkj.symm, hlj.symm, hkl]
  · rwa [iSup_four]

end
end ThirteenPlanes.RoundCubics
