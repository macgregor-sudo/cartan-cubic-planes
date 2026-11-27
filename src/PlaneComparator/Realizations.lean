/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PlaneComparator.Core
public import PlaneComparator.FourLines
public import PlaneComparator.ComplexModel
public import ThirteenPlanes.ClosedBlocks.DecompositionPatterns

@[expose] public section

set_option backward.privateInPublic true

/-! Realize the four proper closed decomposition patterns on real Euclidean spaces. -/

namespace Challenge

open ThirteenPlanes ThirteenPlanes.RoundCubics ThirteenPlanes.ClosedBlocks ThirteenPlanes.Peirce
open scoped InnerProductSpace

noncomputable section

namespace Bridge

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : SymmetricCubic V} {ι : Type*} [Fintype ι] {n : ℕ}

/-- A metric chart to the real Euclidean space of the given dimension. -/
private def euclideanChart (dim : Module.finrank ℝ V = n) :
    V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr dim)).repr

private def euclideanCubic (h : SymmetricCubic V) (dim : Module.finrank ℝ V = n) :
    SymmetricCubic (EuclideanSpace ℝ (Fin n)) :=
  h.pullback (euclideanChart dim).symm.toLinearMap

private theorem euclideanCubic_pullback (dim : Module.finrank ℝ V = n) :
    h = (euclideanCubic h dim).pullback (euclideanChart dim).toLinearMap := by
  apply SymmetricCubic.ext
  intro x y z
  simp [euclideanCubic, SymmetricCubic.pullback_apply]

private def euclideanBlocks (D : Decomposition h ι) (dim : Module.finrank ℝ V = n) :
    Decomposition (euclideanCubic h dim) ι :=
  D.mapIsometry (euclideanChart dim) (euclideanCubic_pullback dim)

omit [Fintype ι] in
private theorem euclideanBlocks_finrank (D : Decomposition h ι)
    (dim : Module.finrank ℝ V = n) (i : ι) :
    Module.finrank ℝ ((euclideanBlocks D dim).piece i) = Module.finrank ℝ (D.piece i) :=
  D.mapIsometry_finrank _ _ i

omit [FiniteDimensional ℝ V] in
private theorem proper_decomposition (D : Decomposition h ι) (proper : 1 < Fintype.card ι) :
    ProperClosedDecomposition (fromSymmetric h) D.piece :=
  ⟨⟨D.orthogonal, D.exhaustive⟩, fun i => ⟨D.nonzero i, D.closed i⟩, proper⟩

private theorem euclideanEikonal (round : IsRound h 1) (dim : Module.finrank ℝ V = n) :
    Eikonal (fromSymmetric (euclideanCubic h dim)) 1 := by
  rw [eikonal_iff, toSymmetric_fromSymmetric]
  exact RoundCubics.IsRound.pullback_isometry round (euclideanChart dim).symm

omit [FiniteDimensional ℝ V] in
private theorem unitNormalize_diagonal (h : SymmetricCubic V) (c : ℝ) (x : V) :
    (unitNormalize h c).apply x x x = (Real.sqrt c)⁻¹ * h.apply x x x :=
  SymmetricCubic.apply_smul _ _ _ _ _

private theorem complex_round : IsRound complexCartanCubic 1 := by
  refine ⟨by norm_num, fun x => ?_⟩
  rw [complexCartanCubic, SymmetricCubic.squareMap_smul, norm_smul, mul_pow,
    Real.norm_of_nonneg (Real.sqrt_nonneg 6), Real.sq_sqrt (by norm_num),
    matrixEqualCubic_squareMap, ThirteenPlanes.TracelessHermitian3.square_norm_sq]
  ring

private theorem complex_dim : Module.finrank ℝ ThirteenPlanes.TracelessHermitian3 = 8 := by
  rw [← complexCartanEquiv.finrank_eq]
  norm_num [Module.finrank_prod, Complex.finrank_real_complex]

private theorem four_plane_witness :
    ∃ (d : Cubic (EuclideanSpace ℝ (Fin 8))) (U : Fin 4 → Submodule ℝ (EuclideanSpace ℝ (Fin 8))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 4 2 := by
  obtain ⟨D, hD⟩ := exists_complex_four_plane_decomposition
  let P := euclideanBlocks D complex_dim
  refine ⟨fromSymmetric _, P.piece, euclideanEikonal complex_round complex_dim,
    proper_decomposition P (by simp), by simp, fun i => ?_⟩
  exact (euclideanBlocks_finrank D complex_dim i).trans (hD i)

private abbrev nativeStrength : ℝ := 1 / 6

private theorem root_ne_zero : Real.sqrt nativeStrength ≠ 0 :=
  (Real.sqrt_pos.mpr (by norm_num)).ne'

private theorem thirteen_plane_witness :
    ∃ (d : Cubic (EuclideanSpace ℝ (Fin 26))) (U : Fin 13 → Submodule ℝ (EuclideanSpace ℝ (Fin 26))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 13 2 := by
  obtain ⟨D, hD⟩ := exists_nativeAlbert_thirteen_plane_decomposition
  let Dn : Decomposition (unitNormalize nativeEqualCubic nativeStrength) (Fin 13) :=
    D.smul (inv_ne_zero root_ne_zero)
  let P := euclideanBlocks Dn nativeTraceless_finrank
  refine ⟨fromSymmetric _, P.piece, euclideanEikonal (unitNormalize_isRound Graded.nativeRound) _,
    proper_decomposition P (by simp), by simp, fun i => ?_⟩
  exact (euclideanBlocks_finrank Dn nativeTraceless_finrank i).trans (hD i)

private theorem octet_and_nine_witness :
    ∃ (d : Cubic (EuclideanSpace ℝ (Fin 26))) (U : Fin 10 → Submodule ℝ (EuclideanSpace ℝ (Fin 26))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ OctetAndNine d U 1 := by
  obtain ⟨D, hdim, hothers, J, hJ⟩ := exists_nativeAlbert_octet_nine_planes
  let d := unitNormalize nativeEqualCubic nativeStrength
  let Dn : Decomposition d (Fin 10) := D.smul (inv_ne_zero root_ne_zero)
  let I := euclideanChart nativeTraceless_finrank
  let P := euclideanBlocks Dn nativeTraceless_finrank
  let K : D.piece 0 ≃ₗᵢ[ℝ] P.piece 0 := mapBlockIsometry I (D.piece 0)
  refine ⟨fromSymmetric _, P.piece, euclideanEikonal (unitNormalize_isRound Graded.nativeRound) _,
    proper_decomposition P (by simp), ?_⟩
  refine ⟨by simp, 0, (euclideanBlocks_finrank Dn nativeTraceless_finrank 0).trans hdim,
    fun j hj => (euclideanBlocks_finrank Dn nativeTraceless_finrank j).trans (hothers j hj), ?_⟩
  let L := K.symm.trans J
  refine ⟨L.toLinearEquiv.trans complexModel, fun x y => ?_, fun x => ?_⟩
  · change ⟪x, y⟫_ℝ = (Matrix.trace
      (complexMatrix (complexModel (L x)) * complexMatrix (complexModel (L y)))).re
    rw [complexModel_tracePairing]
    have hm := norm_add_sq_real (L x) (L y)
    rw [← L.map_add, L.norm_map, L.norm_map, L.norm_map] at hm
    nlinarith only [hm, norm_add_sq_real x y]
  · have hx : I.symm (x : EuclideanSpace ℝ (Fin 26)) = (K.symm x : NativeTraceless) := by
      have hk := mapBlockIsometry_coe I (D.piece 0) (K.symm x)
      change ((K (K.symm x) : P.piece 0) : EuclideanSpace ℝ (Fin 26)) =
        I (K.symm x : NativeTraceless) at hk
      rw [LinearIsometryEquiv.apply_symm_apply] at hk
      rw [hk, LinearIsometryEquiv.symm_apply_apply]
    change (d.pullback I.symm.toLinearMap).apply x x x =
      Real.sqrt (6 * 1) * (Matrix.trace (complexMatrix (complexModel (J (K.symm x))) ^ 3)).re
    rw [SymmetricCubic.pullback_apply]
    change d.apply (I.symm (x : EuclideanSpace ℝ (Fin 26))) (I.symm x) (I.symm x) = _
    rw [hx, unitNormalize_diagonal]
    have he : nativeEqualCubic.apply (K.symm x) (K.symm x) (K.symm x) =
        Real.sqrt nativeStrength * complexCartanCubic.apply (J (K.symm x)) (J (K.symm x)) (J (K.symm x)) := by
      have hp := congrArg (fun h : SymmetricCubic (D.piece 0) =>
        h.apply (K.symm x) (K.symm x) (K.symm x)) hJ
      simpa only [SymmetricCubic.pullback_apply, SymmetricCubic.apply_smul, Submodule.subtype_apply,
        LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using hp
    rw [he, ← mul_assoc, inv_mul_cancel₀ root_ne_zero, one_mul, mul_one, complexModel_matrix]
    exact complexCartanCubic_diagonal _

end Bridge

open Bridge

theorem closed_decomposition_realizations :
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 4))) (U : Fin 4 → Submodule ℝ (EuclideanSpace ℝ (Fin 4))),
      Eikonal d 1 ∧ ¬ Harmonic d ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 4 1) ∧
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 8))) (U : Fin 4 → Submodule ℝ (EuclideanSpace ℝ (Fin 8))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 4 2) ∧
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 26))) (U : Fin 13 → Submodule ℝ (EuclideanSpace ℝ (Fin 26))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 13 2) ∧
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 26))) (U : Fin 10 → Submodule ℝ (EuclideanSpace ℝ (Fin 26))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ OctetAndNine d U 1) := by
  refine ⟨?_, four_plane_witness, thirteen_plane_witness, octet_and_nine_witness⟩
  obtain ⟨h, D, hr, hf, hdim⟩ := four_lines_witness
  refine ⟨fromSymmetric h, D.piece, ?_, ?_, proper_decomposition D (by simp), by simp, hdim⟩
  · simpa only [eikonal_iff, toSymmetric_fromSymmetric] using hr
  · simpa only [harmonic_iff, toSymmetric_fromSymmetric] using hf

end
end Challenge
