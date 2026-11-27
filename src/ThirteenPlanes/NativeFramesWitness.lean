/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.NativeFrames
public import ThirteenPlanes.NativeFramesWitnessPoints
public import ThirteenPlanes.NativeFramesWitnessVerification

@[expose] public section

set_option backward.privateInPublic true

/-! The exact 39 points of the reference code.
The finite tests use kernel reduction in the rational-quadratic coefficient algebra. -/

noncomputable section

namespace ThirteenPlanes.NativeWitness

open ExactAlgebra ExactVerification Data

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem exactFrames (f : Fin 13) : ExactFrame (points f) := by
  fin_cases f <;> unfold ExactFrame <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem exactUpperPairings (f : Fin 13) :
    ∀ g : Fin 13, f < g → ∀ a b : Fin 3, inner (points f a) (points g b) = rational (1/3) := by
  fin_cases f <;> decide +kernel

/-- An actual tight 39-point code in the compact native carrier. -/
/- Cohn, Kumar and Minton proved existence of a tight 39-point code in the Cayley plane
(arXiv:1308.3188, §8.2, Theorem 8.3). This Lean witness uses exact coordinates drawn
from the earlier global cubic sparsity formalization. -/
def referenceCode : TightNativeCode where
  point := nativePoints
  frame f := native_frame _ (exactFrames f)
  overlap {f g} hfg a b := by
    rcases lt_or_gt_of_ne hfg with h | h
    · simpa [nativePoints] using native_pairing _ _ (1/3) (exactUpperPairings f g h a b)
    · rw [Glennie.inner_comm]
      simpa [nativePoints] using native_pairing _ _ (1/3) (exactUpperPairings g f h b a)

theorem referencePoints_injective :
    Function.Injective (fun ab : Fin 13 × Fin 3 => nativePoints ab.1 ab.2) :=
  referenceCode.points_injective

theorem exists_tightNativeCode : Nonempty TightNativeCode :=
  ⟨referenceCode⟩

end ThirteenPlanes.NativeWitness
