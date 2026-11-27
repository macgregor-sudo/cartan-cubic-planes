/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.CompactCartanRegular
public import ThirteenPlanes.Cartan.CompactAdjointOrbit

@[expose] public section

/-! Conjugacy and equal dimension of Cartan subalgebras for the negative Killing metric. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K] [Module.Finite ℝ K]

/-- The compact Cartans of a finite-dimensional real Lie algebra with negative-definite
Killing form are conjugate by a Lie automorphism. -/
theorem compactCartans_conjugate (hK : CompactKilling K)
    (T U : LieSubalgebra ℝ K) (hT : IsCompactCartan T) (hU : IsCompactCartan U) :
    ∃ g : K ≃ₗ⁅ℝ⁆ K, T.map g.toLieHom = U := by
  obtain ⟨x, _, regularT⟩ := compactCartan_exists_centralizer hK T hT
  obtain ⟨y, _, regularU⟩ := compactCartan_exists_centralizer hK U hU
  obtain ⟨g, hxy⟩ := compactKilling_exists_lieEquiv_commutes hK x y
  have hxU : g x ∈ U := (regularU (g x)).mp (by rw [← lie_skew y (g x), hxy, neg_zero])
  have hUle : U ≤ T.map g.toLieHom := by
    intro z hz
    have hc := (hU (g x)).2 hxU z hz
    obtain ⟨w, rfl⟩ := g.surjective z
    refine ⟨w, (regularT w).mp (g.injective ?_), rfl⟩
    change g ⁅x, w⁆ = g 0
    change ⁅g x, g w⁆ = 0 at hc
    rw [g.map_lie, map_zero, hc]
  refine ⟨g, le_antisymm ?_ hUle⟩
  rintro _ ⟨a, ha, rfl⟩
  apply (hU (g a)).1
  intro z hz
  obtain ⟨b, hb, rfl⟩ := hUle hz
  change ⁅g a, g b⁆ = 0
  rw [← g.map_lie, (hT a).2 ha b hb, map_zero]

/-- In a compact real Lie algebra all compact Cartans have the same dimension. -/
theorem compactCartans_finrank_eq (hK : CompactKilling K)
    (T U : LieSubalgebra ℝ K) (hT : IsCompactCartan T) (hU : IsCompactCartan U) :
    Module.finrank ℝ T = Module.finrank ℝ U := by
  obtain ⟨g, rfl⟩ := compactCartans_conjugate hK T U hT hU
  exact (g.toLinearEquiv.finrank_map_eq T.toSubmodule).symm

/-- The ordinary Cartan subalgebras are conjugate under the negative-definite Killing hypothesis. -/
theorem compactCartanSubalgebras_conjugate (hK : CompactKilling K)
    (T U : LieSubalgebra ℝ K) (hT : T.IsCartanSubalgebra) (hU : U.IsCartanSubalgebra) :
    ∃ g : K ≃ₗ⁅ℝ⁆ K, T.map g.toLieHom = U :=
  compactCartans_conjugate hK T U ((compactCartan_iff_cartan hK T).mpr hT)
    ((compactCartan_iff_cartan hK U).mpr hU)

/-- The equal-dimension theorem for the ordinary nilpotent self-normalizing Cartan predicate. -/
theorem compactCartanSubalgebras_finrank_eq (hK : CompactKilling K)
    (T U : LieSubalgebra ℝ K) (hT : T.IsCartanSubalgebra) (hU : U.IsCartanSubalgebra) :
    Module.finrank ℝ T = Module.finrank ℝ U :=
  compactCartans_finrank_eq hK T U ((compactCartan_iff_cartan hK T).mpr hT)
    ((compactCartan_iff_cartan hK U).mpr hU)

end
end ThirteenPlanes.Cartan
