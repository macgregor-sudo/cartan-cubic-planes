/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PlaneComparator.Core
public import PlaneComparator.ComplexModel
public import PlaneComparator.FourLines
public import ThirteenPlanes.ClosedBlocks.AllRoundDecompositions

@[expose] public section

/-! The four decomposition patterns on the challenge's actual block spaces. -/

open scoped RealInnerProductSpace

namespace Challenge

open ThirteenPlanes ThirteenPlanes.RoundCubics

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι]

theorem Bridge.octet_form (d : Cubic V) (U : Submodule ℝ V) {c : ℝ}
    (I : U ≃ₗᵢ[ℝ] ThirteenPlanes.TracelessHermitian3)
    (heq : (Bridge.toSymmetric d).pullback U.subtype =
      Real.sqrt c • Peirce.complexCartanCubic.pullback (W := ↥U) I.toLinearMap) :
    ComplexCartanForm (fun x : U => d.eval x) (Real.sqrt (6 * c)) := by
  simpa only [SymmetricCubic.pullback_apply, Submodule.subtype_apply, Bridge.eval_toSymmetric] using
    Bridge.complex_form_of_cubic ((Bridge.toSymmetric d).pullback U.subtype) I heq

/-- Theorem A(ii). Every proper closed decomposition has one of the four patterns. -/
/- This transports the closed-decomposition classification to the standalone statement's
cubic and block definitions. The native proof includes Vladimir Tkachev's nonharmonic
eikonal alternative (arXiv:1001.2387v2, Theorem 1.1). -/
theorem closed_decomposition_classification
    (d : Cubic V) (c : ℝ) (U : ι → Submodule ℝ V)
    (hd : Eikonal d c) (hU : ProperClosedDecomposition d U) :
    (Module.finrank ℝ V = 4 ∧ ¬ Harmonic d ∧ BlocksOfDimension U 4 1) ∨
    (Module.finrank ℝ V = 8 ∧ BlocksOfDimension U 4 2) ∨
    (Module.finrank ℝ V = 26 ∧ (BlocksOfDimension U 13 2 ∨ OctetAndNine d U c)) := by
  classical
  let D := Bridge.blockDecomp hU.1 (fun i => (hU.2.1 i).1) (fun i => (hU.2.1 i).2)
  have hr := (Bridge.eikonal_iff d c).mp hd
  have pattern := ClosedBlocks.classifyRoundDecompositions D hr hU.2.2
  rcases pattern with h4 | ⟨_, harmonicBlocks⟩
  · exact Or.inl ⟨h4.1, fun h => h4.2.1 ((Bridge.harmonic_iff d).mp h), h4.2.2⟩
  · unfold ClosedBlocks.HarmonicBlockDecompositionPattern at harmonicBlocks
    rcases harmonicBlocks with h8 | ⟨h26, h13 | ⟨h10, i, h8, h2, I, hI⟩⟩
    · exact Or.inr (Or.inl h8)
    · exact Or.inr (Or.inr ⟨h26, Or.inl h13⟩)
    · exact Or.inr (Or.inr ⟨h26, Or.inr ⟨h10, i, h8, h2, Bridge.octet_form d (U i) I hI⟩⟩)

end

end Challenge
