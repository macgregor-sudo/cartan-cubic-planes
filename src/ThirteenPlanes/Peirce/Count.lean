module

public import ThirteenPlanes.ClosedBlocks.Transport
public import ThirteenPlanes.Quaternionic.CapacityCorollaries

@[expose] public section

/-! The exact number of closed planes in a round orthogonal decomposition. -/

open scoped InnerProductSpace

namespace ThirteenPlanes.Peirce

open RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] {h : SymmetricCubic V} {c : ℝ} {planes : PlaneDecomposition V ι}

/-- Theorem count, at arbitrary positive strength. The seven-plane branch
would give seven actual orthogonal closed quaternionic trace planes. -/
theorem planeCount_one_four_thirteen (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (hm : 1 ≤ Fintype.card ι) : Fintype.card ι = 1 ∨ Fintype.card ι = 4 ∨ Fintype.card ι = 13 := by
  rcases planeCount_one_four_seven_thirteen round closed hm with h | h | hseven | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exfalso
    let g := unitNormalize h c
    have gr : IsRound g 1 := unitNormalize_isRound round
    have gc : IsClosedPlaneSystem g planes := by
      intro i
      exact (isClosedPiece_smul_iff (h := h) (inv_ne_zero
        (Real.sqrt_pos.mpr round.positive).ne') (planes.plane i)).mpr (closed i)
    let j : Fin 7 ≃ ι := Fintype.equivFinOfCardEq hseven |>.symm
    obtain ⟨I, hI, _⟩ := closedPlaneSystem_quaternion gr gc hseven (j 0)
    let U (i : Fin 7) := (planes.plane (j i)).map I.toLinearMap
    have hdim (i : Fin 7) : Module.finrank ℝ (U i) = 2 :=
      (I.toLinearEquiv.finrank_map_eq _).trans (planes.dimension (j i))
    have ho : Pairwise fun i j : Fin 7 => (U i).IsOrtho (U j) :=
      fun i k hik => isOrtho_map_isometry I (planes.pairwise_orthogonal (j.injective.ne hik))
    apply QuaternionicMUB.no_seven_closedNativePlanes U hdim ho
    intro i
    have hscaled : IsClosedPiece quaternionCartanCubic (U i) := isClosedPiece_map_isometry I hI (gc (j i))
    exact (isClosedPiece_smul_iff (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne' (U i)).mp hscaled
  · exact Or.inr (Or.inr h)

end ThirteenPlanes.Peirce
