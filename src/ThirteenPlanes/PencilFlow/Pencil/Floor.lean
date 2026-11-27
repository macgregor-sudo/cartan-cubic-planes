module

public import ThirteenPlanes.PencilFlow.Pencil.Contractions

@[expose] public section

/-! The spherical variance and potential, the pencil hypotheses of part (b): every member of the intrinsic
pencil of a closed round plane system is harmonic and has scalar double contraction. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.PencilFlow.Pencil

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Both cubics of the intrinsic pencil are trace-free. -/
theorem closedPencil_traceFree {ι : Type*} [Fintype ι] {h : SymmetricCubic V} {c : ℝ}
    {planes : PlaneDecomposition V ι} (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) :
    (planePencil h planes).diagonalCubic.TraceFree ∧
      (planePencil h planes).mixingCubic.TraceFree := by
  have data := planePencil_hasPlaneData round closed
  have hD : (planePencil h planes).diagonalCubic.TraceFree :=
    fun z => PlaneContractions.trace_L_diag data z
  have hd := PlaneContractions.traceFree_interaction data
  rw [planePencil_at_one] at hd
  refine ⟨hD, fun z => ?_⟩
  change LinearMap.trace ℝ V ((h - (planePencil h planes).diagonalCubic).L z) = 0
  rw [map_sub, LinearMap.sub_apply, map_sub, hd z, hD z, sub_zero]

end

end ThirteenPlanes.PencilFlow.Pencil

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements

/-- The spherical variance and potential: the harmonic and isotropic hypotheses of the two-term floor
hold on the entire pencil. -/
theorem pencilFloorConditions (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.PencilFloorConditions V := by
  intro m _ h c planes round closed u
  obtain ⟨hD, hM⟩ := Pencil.closedPencil_traceFree round closed
  refine ⟨traceFree_coupling hD hM u, ?_⟩
  exact ⟨_, (Pencil.closedPencil_contractions h c planes round closed u.1 u.2).1⟩

end ThirteenPlanes.PencilFlow.Proofs
