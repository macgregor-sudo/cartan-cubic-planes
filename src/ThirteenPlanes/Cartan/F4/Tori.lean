/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.F4.GradedCartanCasimir
public import ThirteenPlanes.Cartan.F4.ChargePlaneScalar
public import ThirteenPlanes.Cartan.F4.CasimirScalar
public import ThirteenPlanes.Cartan.F4.CartanConjugacy
public import ThirteenPlanes.Cartan.F4.CartanInterfaces

@[expose] public section

set_option backward.privateInPublic true

/-! Every ordinary Cartan in the native compact Albert derivations is of frame type. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading

noncomputable section

private theorem signedPlaneIndex_nontrivial : Nontrivial SignedPlaneIndex :=
  Fintype.one_lt_card_iff_nontrivial.mp (by rw [signedPlaneIndex_card]; decide)

private theorem nativeGradedPlane_finrank (q : SignedPlaneIndex) :
    Module.finrank ℝ (nativeGradedPlane q) = 2 :=
  (albertTraceEquiv.symm.toLinearEquiv.submoduleMap
    (pointPlane Graded.nativeGradingHom q)).finrank_eq.symm.trans
    (pointPlane_finrank nativeGradingHom_isTernaryGrading q)

private theorem nativeGradedCasimir_uniform (p : SignedPlaneIndex) :
    ∃ a : ℝ, ∀ q ≠ p, ∀ x ∈ nativeGradedPlane q, nativeGradedCasimir p x = a • x := by
  have hscalar (q : SignedPlaneIndex) :
      ∃ a : ℝ, ∀ x ∈ nativeGradedPlane q, nativeGradedCasimir p x = a • x :=
    nativeChargeEquivariant_symmetric_scalar_on_plane (nativeGradedCasimir p)
      (nativeGradedCasimir_intertwines_charges p) (nativeGradedCasimir_isSymmetric p) q
  let := signedPlaneIndex_nontrivial
  obtain ⟨q, hq⟩ := exists_ne p
  obtain ⟨a, ha⟩ := hscalar q
  refine ⟨a, ?_⟩
  intro r hr x hx
  obtain ⟨b, hb⟩ := hscalar r
  obtain ⟨e, he, hmap⟩ := nativeGradedCasimir_offPoint_symmetry p q r hq hr
  have hq' : nativeGradedPlane q ≠ ⊥ := by
    intro hz
    have hh := nativeGradedPlane_finrank q
    rw [hz, finrank_bot] at hh
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq'
  have hab : a • e y = b • e y := by
    rw [← e.map_smul, ← ha y hy, ← he, hb (e y) (hmap y hy)]
  have hne : e y ≠ 0 := by
    intro h
    exact hy0 (e.injective (h.trans e.map_zero.symm))
  exact (smul_left_injective ℝ hne hab).symm ▸ hb x hx

/-- Each reference graded Cartan has the exact frame-type trace Casimir. -/
theorem nativeGradedCartan_frameType (p : SignedPlaneIndex) :
    IsFrameType (nativeAlbertRestrictedCartan (nativeGradedCartan p)) 4 (1 / 6) := by
  obtain ⟨a, ha⟩ := nativeGradedCasimir_uniform p
  exact nativeAlbertFrameType_of_scalar_pointPlanes nativeGradingHom_isTernaryGrading p _
    (nativeGradedCartan_commutative p) (nativeGradedCartan_finrank p)
    (nativeGradedCartan_fixedSpace p) a ha

/-- The paper's frame-type conclusion for every actual ordinary compact Albert Cartan. -/
/- The paper uses Yokota's descriptions of the rank-four compact F₄ and diagonal
Spin(8) action (arXiv:0902.0431, Theorems 2.6.1, 1.14.2, 2.7.1, and Proposition 2.3.7).
This proof transports the computed frame-type Casimir of a reference graded Cartan
under an actual compact Albert automorphism. -/
theorem nativeAlbertCartan_frameType (T : LieSubalgebra ℝ NativeAlbertDerivations)
    (hT : T.IsCartanSubalgebra) :
    IsFrameType (nativeAlbertRestrictedCartan T) 4 (1 / 6) := by
  let := signedPlaneIndex_nontrivial
  let p : SignedPlaneIndex := Classical.choice inferInstance
  obtain ⟨g, h⟩ := nativeAlbertCartans_conjugate (nativeGradedCartan p) T
    (nativeGradedCartan_isCartan p) hT
  rw [← h]
  exact nativeAlbertCartan_frameType_map g _ (nativeGradedCartan_frameType p)

/-- The represented Cartan form of the frame-type theorem, used by the second-row correspondence. -/
theorem albertCartans_frameType : AlbertCartansFrameType :=
  albertCartansFrameType_of_native
    (nativeAlbert_compactKilling_of_grading nativeGradingHom_isTernaryGrading)
    nativeAlbertCartan_frameType

/-- The frame type of compact F₄ Cartans on maximal commutative spaces of the actual Albert derivations. -/
theorem compactF4Tori_frameType : CompactF4ToriFrameType :=
  compactF4ToriFrameType_iff_albertCartansFrameType.mpr albertCartans_frameType

end

end ThirteenPlanes.Cartan
