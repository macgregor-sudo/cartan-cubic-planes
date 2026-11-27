module

public import ThirteenPlanes.Nonharmonic.AxialNormalForm
public import ThirteenPlanes.ClosedBlocks.Transport
public import ThirteenPlanes.RoundContractions
public import ThirteenPlanes.Peirce.UnitIdempotent
public import ThirteenPlanes.Nonharmonic.TraceDichotomy
public import ThirteenPlanes.Nonharmonic.AxialCoordinates
public import ThirteenPlanes.Nonharmonic.TraceCompression

@[expose] public section

/-! The nonharmonic classification for all positive-strength round cubics. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open Nonharmonic Peirce RoundCubics

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A nonharmonic finite-dimensional real eikonal cubic is the scaled axial cubic. -/
/- This proves the nonharmonic alternative of Vladimir Tkachev (arXiv:1001.2387v2,
Theorem 1.1). A trace contraction of the Peirce pair identity separates the zero-trace
and scalar-action cases, and an axis rotation gives the axial cubic in the latter case. -/
theorem tkachevNonharmonic : TkachevNonharmonic V := by
  intro h c round htrace
  by_cases hV : Nontrivial V
  · let : Nontrivial V := hV
    let g := unitNormalize h c
    have gr : IsRound g 1 := unitNormalize_isRound round
    have heq : h = Real.sqrt c • g := eq_smul_unitNormalize round
    have hscale : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr round.positive).ne'
    have hgt : ¬ g.TraceFree := by
      intro tf
      apply htrace
      rw [heq]
      exact (traceFree_smul_iff g hscale).2 tf
    obtain ⟨a, ha⟩ := exists_unitIdempotent g gr
    have normal : ∃ e : V, ‖e‖ = 1 ∧ ∀ x : V,
        let s := ⟪x, e⟫
        g.apply x x x = s ^ 3 - 3 * s * ‖x - s • e‖ ^ 2 := by
      by_cases hH : halfSpace g a = ⊥
      · exact ⟨a, ha.1, normalForm_of_half_bot g gr ha hH⟩
      · have hhalf : Nontrivial (halfSpace g a) := Submodule.nontrivial_iff_ne_bot.mpr hH
        rcases traceDichotomy g gr ha hhalf with ⟨hA, hM⟩ | ⟨u, hu, hm, r, hr, hs⟩
        · exact (hgt (traceFree_of_balanced gr ha hA hM)).elim
        · let e : V := (-1 / 2 : ℝ) • a - r • (u : V)
          exact ⟨e, normalForm_of_minus_line g gr ha u hu hm hr hs⟩
    obtain ⟨e, he, hn⟩ := normal
    have hdim : Module.finrank ℝ V ≠ 2 :=
      fun hd => htrace (traceFree_of_round_finrank_two round hd)
    refine ⟨hdim, e, he, fun x => ?_⟩
    dsimp only
    rw [heq, SymmetricCubic.apply_smul]
    exact congrArg (Real.sqrt c * ·) (hn x)
  · let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exfalso
    apply htrace
    intro x
    rw [Subsingleton.elim x 0, map_zero, map_zero]

end

end ThirteenPlanes.ClosedBlocks
