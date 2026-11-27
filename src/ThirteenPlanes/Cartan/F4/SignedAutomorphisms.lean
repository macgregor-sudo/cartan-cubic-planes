/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.F4.ChargeAction
public import ThirteenPlanes.Cartan.GradedActionWitness
public import ThirteenPlanes.Cartan.GradedRecutAction
public import ThirteenPlanes.Recovery.JordanExtension
public import ThirteenPlanes.FiniteGroup.CodeLifts

@[expose] public section

set_option backward.privateInPublic true

/-! Native lifts of the signed cubic symmetries and their character covariance. -/

namespace ThirteenPlanes.Cartan

open scoped RealInnerProductSpace BigOperators
open RoundCubics FiniteGroup Matrix
open AlbertGrading.Grading

noncomputable section

set_option maxHeartbeats 800000 in
private def fullAlbertCubic : SymmetricCubic Glennie.Albert :=
  SymmetricCubic.ofProduct albertJordan.L albertJordan.comm (by
    intro x y z
    rw [albertJordan.assoc_inner x y z, real_inner_comm])

set_option maxHeartbeats 1200000 in
private theorem fullAlbertCubic_trace (x y z : RoundCubics.traceZero (1 : Glennie.Albert)) :
    (RoundCubics.traceCubic fullAlbertCubic (1 : Glennie.Albert)).apply x y z =
      nativeEqualCubic.apply (albertTraceEquiv x) (albertTraceEquiv y) (albertTraceEquiv z) := by
  rw [traceCubic, SymmetricCubic.pullback_apply]
  simp only [fullAlbertCubic, nativeEqualCubic, SymmetricCubic.apply_ofProduct,
    Submodule.subtype_apply, nativeCenteredJordan_apply]
  have h : ⟪nativeCenter (Glennie.jordan x.val y.val), albertTraceEquiv z⟫ =
      ⟪Glennie.jordan x.val y.val, z.val⟫ := by
    change ⟪Glennie.traceless (Glennie.jordan x.val y.val), z.val⟫ =
      ⟪Glennie.jordan x.val y.val, z.val⟫
    simp only [Glennie.hilbert_inner_eq_native]
    exact nativeInner_center_left _ (albertTraceEquiv z)
  change ⟪Glennie.jordanLinear x.val y.val, z.val⟫ = _
  rw [Glennie.jordanLinear_apply]
  have hx : (albertTraceEquiv x).val = x.val := albertTraceEquiv_val x
  have hy : (albertTraceEquiv y).val = y.val := albertTraceEquiv_val y
  rw [hx, hy]
  exact h.symm

set_option maxHeartbeats 2000000 in
/-- A signed cubic symmetry lifts to the actual full compact Albert algebra. -/
theorem exists_albertSignedLift (R : Relabeling) (hR : R.PreservesCubic) :
    ∃ g : Glennie.CompactAutomorphism, ∀ x : SignedField,
      g.equiv (signedNativeEquiv x).val = (signedNativeEquiv (R.toIsometry x)).val := by
  let i : SignedField ≃ₗᵢ[ℝ] RoundCubics.traceZero (1 : Glennie.Albert) :=
    signedNativeEquiv.trans albertTraceEquiv.symm
  let W := i.symm.trans (R.toIsometry.trans i)
  have hi (x : SignedField) : albertTraceEquiv (i x) = signedNativeEquiv x :=
    albertTraceEquiv.apply_symm_apply (signedNativeEquiv x)
  have hWi (x : SignedField) : W (i x) = i (R.toIsometry x) := by simp [W]
  have hW : cubicPreserved (RoundCubics.traceCubic fullAlbertCubic (1 : Glennie.Albert)) W := by
    apply (cubicPreserved_iff W).mpr
    intro x y z
    obtain ⟨x, rfl⟩ := i.surjective x
    obtain ⟨y, rfl⟩ := i.surjective y
    obtain ⟨z, rfl⟩ := i.surjective z
    rw [hWi, hWi, hWi, fullAlbertCubic_trace, fullAlbertCubic_trace]
    simp only [hi, ← signedEqualCubic_eq_native]
    exact hR x y z
  have he : ⟪(1 : Glennie.Albert), (1 : Glennie.Albert)⟫ = 3 := albertJordan.unit_trace
  have hu' (x : Glennie.Albert) : fullAlbertCubic.L (1 : Glennie.Albert) x = x := by
    simp only [fullAlbertCubic, SymmetricCubic.L_ofProduct]
    exact albertJordan.unit_left x
  obtain ⟨F, _, hp, ht, hF⟩ := (traceCubic_stabilizer_iff he hu' W).mp hW
  have hp' (x y : Glennie.Albert) :
      F (Glennie.jordan x y) = Glennie.jordan (F x) (F y) := by
    simpa only [fullAlbertCubic, SymmetricCubic.L_ofProduct, albertJordan,
      Glennie.jordanLinear_apply] using hp x y
  refine ⟨{ equiv := F, map_jordan := hp', map_trace := ?_ }, ?_⟩
  · intro x
    simpa only [Glennie.hilbert_inner_eq_native, nativeInner_one_left] using ht x
  · intro x
    change F (i x).val = (i (R.toIsometry x)).val
    rw [hF, hWi]

/-- The contragredient parameter change for a relabeling of the grades. -/
theorem chargeDot_transpose_mulVec (A : ChargeMatrix) (s q : Charge) :
    chargeDot s (A *ᵥ q) = chargeDot (Aᵀ *ᵥ s) q := by
  change s ⬝ᵥ (A *ᵥ q) = (Aᵀ *ᵥ s) ⬝ᵥ q
  rw [dotProduct_mulVec, Matrix.mulVec_transpose]

/-- The signed lift intertwines the native charge actions with the contragredient action. -/
theorem albertSignedLift_character (A : SpecialLinearGroup (Fin 3) (ZMod 3))
    (F : Charge → ZMod 3) (hF : IsOddPhase F) (g : Glennie.CompactAutomorphism)
    (hg : ∀ x : SignedField,
      g.equiv (signedNativeEquiv x).val =
        (signedNativeEquiv ((codeRelabeling A F hF).toIsometry x)).val)
    (s : Charge) (x : Glennie.Albert) :
    Graded.nativeCharacterAction s (g.equiv x) =
      g.equiv (Graded.nativeCharacterAction ((A : ChargeMatrix)ᵀ *ᵥ s) x) := by
  let R := codeRelabeling A F hF
  let t : Charge := (A : ChargeMatrix)ᵀ *ᵥ s
  have hc (r : Charge) (X : SignedField) :
      Graded.nativeCharacterAction r (signedNativeEquiv X).val =
        (signedNativeEquiv (chargeAction r X)).val := by
    apply Graded.nativeSignedCoordinates.injective
    apply Subtype.ext
    rw [Graded.nativeCharacterAction_coordinates,
      Graded.nativeSignedCoordinates_signedNative, Graded.nativeSignedCoordinates_signedNative]
    funext q
    change chargePhase (chargeDot r q) * signedExtend X q = signedExtend (chargeAction r X) q
    by_cases hq : q = 0
    · subst q
      simp
    · have h := chargeActionMap_apply r X ⟨q, hq⟩
      rw [← signedExtend_nonzero X ⟨q, hq⟩,
        ← signedExtend_nonzero (chargeActionMap r X) ⟨q, hq⟩] at h
      exact h.symm
  have hR (X : SignedField) : chargeAction s (R.toIsometry X) = R.toIsometry (chargeAction t X) := by
    apply Subtype.ext
    funext y
    change signedCoordinates (chargeActionMap s (R.toLinearMap X)) y =
      signedCoordinates (R.toLinearMap (chargeAction t X)) y
    rw [chargeActionMap_apply, R.coord_toLinearMap, R.coord_toLinearMap,
      R.coordMap_apply, R.coordMap_apply]
    change _ = _ * signedCoordinates (chargeActionMap t X) (R.perm.symm y)
    rw [chargeActionMap_apply]
    have hy : y.val = (A : ChargeMatrix) *ᵥ (R.perm.symm y).val := by
      rw [← chargeAct_val A (R.perm.symm y)]
      exact congrArg Subtype.val (R.perm.apply_symm_apply y).symm
    have hd : chargeWeight s y.val = chargeWeight t (R.perm.symm y).val := by
      change chargeDot s y.val = chargeDot ((A : ChargeMatrix)ᵀ *ᵥ s) (R.perm.symm y).val
      rw [hy, chargeDot_transpose_mulVec]
    rw [hd]
    ring
  have hx : x = (nativeCenter x).val + (Glennie.trace x / 3) • (1 : Glennie.Albert) := by
    change x = x - _ + _
    abel
  obtain ⟨X, hX⟩ := signedNativeEquiv.surjective (nativeCenter x)
  rw [← hX] at hx
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [map_add, map_smul, g.map_unit, Graded.nativeCharacterAction_one,
    hc, hg]
  exact congrArg (fun y : SignedField => (signedNativeEquiv y).val +
    (Glennie.trace x / 3) • (1 : Glennie.Albert)) (hR X)

end

end ThirteenPlanes.Cartan
