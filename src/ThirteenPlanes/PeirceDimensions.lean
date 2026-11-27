module

public import ThirteenPlanes.PeirceDecomposition
public import ThirteenPlanes.RoundContractions
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! Dimension consequences of an exhaustive closed plane system. -/

open scoped BigOperators InnerProductSpace

namespace ThirteenPlanes.Peirce

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι]

/-- The ambient dimension is twice the number of exhaustive orthogonal two-planes. -/
theorem finrank_eq_twice_card (planes : PlaneDecomposition V ι) :
    Module.finrank ℝ V = 2 * Fintype.card ι := by
  classical
  have horth : OrthogonalFamily ℝ (fun i => planes.plane i) (fun i => (planes.plane i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise planes.pairwise_orthogonal
  have hs : Module.finrank ℝ ↥(⨆ i, planes.plane i) = 2 * Fintype.card ι := by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum,
      LinearMap.finrank_range_of_inj horth.independent.dfinsupp_lsum_injective]
    change Module.finrank ℝ (DirectSum ι (fun i => ↥(planes.plane i))) = _
    rw [Module.finrank_directSum]
    simp [planes.dimension, Nat.mul_comm]
  rwa [planes.exhaustive, finrank_top] at hs

/-- Lemma 2b-dims, for a unit idempotent in a plane of the system. -/
theorem closedPlaneDimensions {h : SymmetricCubic V} {a : V} {planes : PlaneDecomposition V ι}
    (round : IsRound h 1) (closed : IsClosedPlaneSystem h planes)
    (ha : IsUnitIdempotent h a) (i : ι) (_ha_plane : a ∈ planes.plane i) :
    let m := Fintype.card ι
    let k := 2 * (m - 1) / 3
    h.TraceFree ∧ m % 3 = 1 ∧ Even k ∧
      Module.finrank ℝ (minusSpace h a) = k + 1 ∧
      Module.finrank ℝ (halfSpace h a) = 2 * k ∧
      Module.finrank ℝ V = 3 * k + 2 := by
  dsimp only
  have ht := RoundCubics.traceFree_of_isClosedPlaneSystem round closed
  have hN := finrank_eq_twice_card planes
  have hm_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨_, hm, hp⟩ := finrank_exact_of_trace_zero round ha (ht a)
  have hmod : Fintype.card ι % 3 = 1 := by omega
  refine ⟨ht, hmod, ?_, ?_, ?_, ?_⟩
  · exact ⟨(Fintype.card ι - 1) / 3, by omega⟩
  all_goals omega

end ThirteenPlanes.Peirce
