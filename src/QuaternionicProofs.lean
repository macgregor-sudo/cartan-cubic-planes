/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CartanCubicPlanes.Definitions
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

import ThirteenPlanes.Quaternionic.FourierNormalForm
import ThirteenPlanes.Quaternionic.CapacityCorollaries

@[expose] public section

namespace Challenge.Quaternionic

open scoped BigOperators Matrix
noncomputable section

private def nativeBasis : Basis ≃ QuaternionicMUB.QBasis where
  toFun U := ⟨U.val, (Unitary.mem_iff.mp U.property).1, (Unitary.mem_iff.mp U.property).2⟩
  invFun U := ⟨U.mat, Unitary.mem_iff.mpr ⟨U.adjoint_mul, U.mul_adjoint⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := QuaternionicMUB.QBasis.eq_of_mat_eq rfl

private theorem native_unbiased (U V : Basis) :
    (nativeBasis U).MutuallyUnbiased (nativeBasis V) ↔ unbiased U V := Iff.rfl

private theorem native_triple (U V W : Basis) :
    QuaternionicMUB.IsUnbiasedTriple (nativeBasis U) (nativeBasis V) (nativeBasis W) ↔
      unbiasedTriple U V W := Iff.rfl

private theorem native_share (U V W : Basis) :
    QuaternionicMUB.basisS (nativeBasis U) (nativeBasis V) (nativeBasis W) = share U V W := rfl

private theorem native_fourier : QuaternionicMUB.fourierBasis.mat = fourier :=
  Matrix.ext QuaternionicMUB.fourierBasis_entry

private theorem native_attainingPhases : QuaternionicMUB.attainmentPhases = attainingPhases :=
  QuaternionicMUB.attainmentPhases_formula

private theorem native_phasedFourier (p : Outcome → Q) (hp : unitPhases p) :
    (QuaternionicMUB.phasedFourierBasis p hp).mat = Matrix.diagonal p * fourier :=
  (QuaternionicMUB.QBasis.product_mat (QuaternionicMUB.diagonalBasis p hp)
    QuaternionicMUB.fourierBasis).trans (congrArg (Matrix.diagonal p * ·) native_fourier)

private theorem native_rightPhases (L U : Basis) (σ : Equiv.Perm Outcome)
    (p : Outcome → Q) (hp : unitPhases p) :
    (((nativeBasis L).product ((nativeBasis U).permuteOutcomes σ)).rightPhases p hp).mat =
      L.val * U.val.submatrix id σ * Matrix.diagonal p := by
  simp only [QuaternionicMUB.QBasis.rightPhases, QuaternionicMUB.QBasis.product_mat]
  rfl

private theorem native_normalForm (U V W : Basis) (p : Outcome → Q) (hp : unitPhases p) :
    normalForm U V W p ↔
      QuaternionicMUB.IsPermutedFourierNormalForm (nativeBasis U) (nativeBasis V) (nativeBasis W) p hp := by
  constructor
  · rintro ⟨L, σ, τ, υ, u, v, w, hu, hv, hw, hU, hV, hW⟩
    refine ⟨σ, τ, υ, nativeBasis L, u, v, w, hu, hv, hw, ?_, ?_, ?_⟩
    · exact QuaternionicMUB.QBasis.eq_of_mat_eq ((native_rightPhases L U σ u hu).trans hU)
    · exact QuaternionicMUB.QBasis.eq_of_mat_eq
        ((native_rightPhases L V τ v hv).trans (hV.trans native_fourier.symm))
    · exact QuaternionicMUB.QBasis.eq_of_mat_eq
        ((native_rightPhases L W υ w hw).trans (hW.trans (native_phasedFourier p hp).symm))
  · rintro ⟨σ, τ, υ, L, u, v, w, hu, hv, hw, hU, hV, hW⟩
    let L' := nativeBasis.symm L
    have hL : nativeBasis L' = L := nativeBasis.apply_symm_apply L
    refine ⟨L', σ, τ, υ, u, v, w, hu, hv, hw, ?_, ?_, ?_⟩
    · rw [← native_rightPhases L' U σ u hu, hL, hU]
      rfl
    · rw [← native_rightPhases L' V τ v hv, hL, hV, native_fourier]
    · rw [← native_rightPhases L' W υ w hw, hL, hW, native_phasedFourier]

/-- The quaternionic lower bound, an attaining triple, and a necessary equality condition in every permuted Fourier normal form. -/
theorem quaternionicLowerBound :
    (∀ U V W : Basis, unbiasedTriple U V W → 1 - 1 / Real.sqrt 3 ≤ share U V W) ∧
    (∃ U V W : Basis, U.val = 1 ∧ V.val = fourier ∧
      W.val = Matrix.diagonal attainingPhases * fourier ∧
      unbiasedTriple U V W ∧ share U V W = 1 - 1 / Real.sqrt 3) ∧
    (∀ U V W : Basis, unbiasedTriple U V W → ∀ p : Outcome → Q, unitPhases p →
      normalForm U V W p → (share U V W = 1 - 1 / Real.sqrt 3 →
        extremalBalance (balance (p 0)) (balance (p 1)) (balance (p 2)))) := by
  obtain ⟨hbound, ⟨hattain, heq⟩, _⟩ := QuaternionicMUB.nativeTripleFloor
  refine ⟨?_, ?_, ?_⟩
  · intro U V W h
    rw [← native_share]
    exact hbound _ _ _ ((native_triple U V W).mpr h)
  · let U := nativeBasis.symm QuaternionicMUB.QBasis.coordinate
    let V := nativeBasis.symm QuaternionicMUB.fourierBasis
    let W := nativeBasis.symm QuaternionicMUB.attainingBasis
    have hU := nativeBasis.apply_symm_apply QuaternionicMUB.QBasis.coordinate
    have hV := nativeBasis.apply_symm_apply QuaternionicMUB.fourierBasis
    have hW := nativeBasis.apply_symm_apply QuaternionicMUB.attainingBasis
    refine ⟨U, V, W, rfl, native_fourier, ?_, ?_, ?_⟩
    · change QuaternionicMUB.attainingBasis.mat = _
      change (QuaternionicMUB.phasedFourierBasis QuaternionicMUB.attainmentPhases
        QuaternionicMUB.attainmentPhases_unit).mat = _
      exact (native_phasedFourier _ QuaternionicMUB.attainmentPhases_unit).trans
        (congrArg (fun p => Matrix.diagonal p * fourier) native_attainingPhases)
    · rw [← native_triple, hU, hV, hW]
      exact hattain
    · rw [← native_share, hU, hV, hW]
      exact heq
  · intro U V W h p hp hf
    have hNative := (native_triple U V W).mpr h
    rw [← native_share, ← QuaternionicMUB.basisGeometricShare_eq_basisS _ _ _
      hNative.1 hNative.2.1 hNative.2.2]
    exact (QuaternionicMUB.quaternionicFloor_equality_withPermutations hNative
      ((native_normalForm U V W p hp).mp hf)).mp

/-- Every set of pairwise unbiased quaternionic bases has at most five members. -/
theorem quaternionicFiveBound (S : Set Basis) (hS : S.Pairwise unbiased) :
    S.Finite ∧ S.ncard ≤ 5 := by
  have hImage : (nativeBasis '' S).Pairwise QuaternionicMUB.QBasis.MutuallyUnbiased := by
    rintro Y ⟨U, hU, rfl⟩ Z ⟨V, hV, rfl⟩ hUV
    exact (native_unbiased U V).mpr (hS hU hV (fun h => hUV (congrArg nativeBasis h)))
  obtain ⟨hfinite, hbound⟩ := QuaternionicMUB.quaternionicFiveBound (nativeBasis '' S) hImage
  exact ⟨hfinite.of_finite_image nativeBasis.injective.injOn,
    (Set.ncard_image_of_injective S nativeBasis.injective) ▸ hbound⟩

end

end Challenge.Quaternionic
