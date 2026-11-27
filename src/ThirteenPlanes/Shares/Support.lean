module

public import ThirteenPlanes.PlaneShares

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {m : ℕ} {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin m)}

def unorderedPlaneShare (h : SymmetricCubic V) (system : PlaneDecomposition V (Fin m))
    (t : IncreasingPlaneTriple m) : ℝ :=
  planeShare h system t.val.1 t.val.2.1 t.val.2.2

/-- The unordered triples whose projection shares are positive. -/
def positivePlaneTriples (h : SymmetricCubic V) (system : PlaneDecomposition V (Fin m)) :
    Finset (IncreasingPlaneTriple m) :=
  Finset.univ.filter (fun t => 0 < unorderedPlaneShare h system t)

theorem unorderedPlaneShare_bounds (t : IncreasingPlaneTriple m) :
    unorderedPlaneShare h system t ∈ Set.Icc (0 : ℝ) 1 :=
  (planeShare_bounds h system ..).1

theorem positivePlaneTriples_sum (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (∑ t ∈ positivePlaneTriples h system, unorderedPlaneShare h system t) =
      (m : ℝ) * ((m : ℝ) - 1) / 3 := by
  rw [positivePlaneTriples, Finset.sum_filter, ← planeShare_total round closed]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with ht
  · rfl
  · exact le_antisymm (le_of_not_gt ht) (unorderedPlaneShare_bounds t).1 |>.symm

/-- At least m(m−1)/3 unordered triples have positive shares. -/
theorem positivePlaneTriples_card_ge (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (m : ℝ) * ((m : ℝ) - 1) / 3 ≤ (positivePlaneTriples h system).card := by
  calc
    _ = ∑ t ∈ positivePlaneTriples h system, unorderedPlaneShare h system t :=
      (positivePlaneTriples_sum round closed).symm
    _ ≤ ∑ _t ∈ positivePlaneTriples h system, (1 : ℝ) :=
      Finset.sum_le_sum fun t _ => (unorderedPlaneShare_bounds t).2
    _ = _ := by simp

/-- The bound on the number of positive unordered triples is saturated exactly for binary shares. -/
theorem positivePlaneTriples_card_eq_iff (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    ((positivePlaneTriples h system).card : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 3 ↔
      ∀ t : IncreasingPlaneTriple m, unorderedPlaneShare h system t = 0 ∨
        unorderedPlaneShare h system t = 1 := by
  have hsum : (∑ t ∈ positivePlaneTriples h system, (1 - unorderedPlaneShare h system t)) =
      ((positivePlaneTriples h system).card : ℝ) - (m : ℝ) * ((m : ℝ) - 1) / 3 := by
    rw [Finset.sum_sub_distrib, positivePlaneTriples_sum round closed]
    simp
  have hz := Finset.sum_eq_zero_iff_of_nonneg
      (s := positivePlaneTriples h system) (f := fun t => 1 - unorderedPlaneShare h system t)
      (fun t _ => sub_nonneg.mpr (unorderedPlaneShare_bounds t).2)
  rw [← sub_eq_zero, ← hsum, hz]
  constructor
  · intro all t
    by_cases ht : 0 < unorderedPlaneShare h system t
    · exact Or.inr ((sub_eq_zero.mp (all t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))).symm)
    · exact Or.inl (le_antisymm (le_of_not_gt ht) (unorderedPlaneShare_bounds t).1)
  · intro all t ht
    have hp := (Finset.mem_filter.mp ht).2
    rw [(all t).resolve_left (ne_of_gt hp), sub_self]

/-- Binary shares of increasing triples are equivalent to binary shares in every distinct order. -/
theorem unorderedPlaneShare_binary_iff (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (∀ t : IncreasingPlaneTriple m, unorderedPlaneShare h system t = 0 ∨
      unorderedPlaneShare h system t = 1) ↔
    ∀ i j k : Fin m, i ≠ j → k ≠ i → k ≠ j →
      planeShare h system i j k = 0 ∨ planeShare h system i j k = 1 := by
  constructor
  · intro hb i j k hij hki hkj
    have b (a b d : Fin m) (hab : a < b) (hbd : b < d) :
        planeShare h system a b d = 0 ∨ planeShare h system a b d = 1 :=
      hb ⟨(a, b, d), hab, hbd⟩
    rcases lt_or_gt_of_ne hij with h₁ | h₁ <;>
      rcases lt_or_gt_of_ne hki with h₂ | h₂ <;>
      rcases lt_or_gt_of_ne hkj with h₃ | h₃
    · rw [← planeShare_cycle round closed hki hij]
      exact b _ _ _ h₂ h₁
    · exact False.elim (not_lt_of_gt h₃ (h₂.trans h₁))
    · rw [planeShare_swap_last round closed hij hki.symm]
      exact b _ _ _ h₂ h₃
    · exact b _ _ _ h₁ h₃
    · rw [← planeShare_cycle round closed hki hij, planeShare_swap_last round closed hki hkj]
      exact b _ _ _ h₃ h₁
    · rw [planeShare_cycle round closed hij hkj.symm]
      exact b _ _ _ h₃ h₂
    · exact False.elim (not_lt_of_gt h₁ (h₂.trans h₃))
    · rw [planeShare_swap_first round closed hij]
      exact b _ _ _ h₁ h₂
  · intro hb t
    exact hb _ _ _ t.property.1.ne (t.property.1.trans t.property.2).ne' t.property.2.ne'

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private theorem thirteenPlane_card_triples : Fintype.card (IncreasingPlaneTriple 13) = 286 := by
  decide

/-- The number of all available triples, their total share, and the lower support bound at m=13.
This is the thirteen-plane support and incidence theorem (i). -/
theorem thirteenPlane_share_counts {system : PlaneDecomposition V (Fin 13)}
    (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    Fintype.card (IncreasingPlaneTriple 13) = 286 ∧
      (∑ t : IncreasingPlaneTriple 13, unorderedPlaneShare h system t) = 52 ∧
      52 ≤ (positivePlaneTriples h system).card := by
  refine ⟨thirteenPlane_card_triples, ?_, ?_⟩
  · norm_num [unorderedPlaneShare, planeShare_total round closed]
  · have hc := positivePlaneTriples_card_ge round closed
    norm_num at hc
    exact_mod_cast hc

/-- The thirteen-plane support and incidence theorem (ii)(a) iff (b). -/
theorem thirteenPlane_positive_eq_fifty_two_iff {system : PlaneDecomposition V (Fin 13)}
    (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (positivePlaneTriples h system).card = 52 ↔
    ∀ i j k : Fin 13, i ≠ j → k ≠ i → k ≠ j →
      planeShare h system i j k = 0 ∨ planeShare h system i j k = 1 := by
  rw [← unorderedPlaneShare_binary_iff round closed, ← positivePlaneTriples_card_eq_iff round closed]
  norm_num
  constructor <;> intro hc <;> exact_mod_cast hc

end
end ThirteenPlanes.RoundCubics
