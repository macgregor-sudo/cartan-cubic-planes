module

public import ThirteenPlanes.Basic

@[expose] public section

/-! The nonharmonic eikonal classification. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

noncomputable section

/-- Every nonharmonic round cubic has the axial normal form, and its dimension is not two. -/
/- The nonharmonic alternative in Vladimir Tkachev's theorem on the cubic eikonal equation
(arXiv:1001.2387v2, Theorem 1.1 and Eq. (3)), with the original positive scale restored. -/
def TkachevNonharmonic (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop :=
  ∀ (h : SymmetricCubic V) (c : ℝ), IsRound h c → ¬ h.TraceFree →
    Module.finrank ℝ V ≠ 2 ∧
    ∃ a : V, ‖a‖ = 1 ∧ ∀ x : V,
      let s := ⟪x, a⟫
      h.apply x x x = Real.sqrt c * (s ^ 3 - 3 * s * ‖x - s • a‖ ^ 2)

end

end ThirteenPlanes.ClosedBlocks
