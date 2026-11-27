/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.F4.GradeTransport
public import ThirteenPlanes.Cartan.F4.FrameTransport
public import ThirteenPlanes.Cartan.F4.PointStabilizer

@[expose] public section

set_option backward.privateInPublic true

/-! Symmetry of the native trace Casimir of the reference graded Cartan. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading FiniteGroup Matrix
open scoped RealInnerProductSpace BigOperators

noncomputable section

/-- The actual homogeneous Cartan for the checked signed ternary action. -/
abbrev nativeGradedCartan (p : SignedPlaneIndex) : LieSubalgebra ℝ NativeAlbertDerivations :=
  albertGradingRealCartan nativeGradingHom_isTernaryGrading p

/-- The fixed-plane carrier of the reference grading in the trace representation. -/
abbrev nativeGradedPlane (p : SignedPlaneIndex) : Submodule ℝ albertJordan.traceFree :=
  (pointPlane Graded.nativeGradingHom p).map albertTraceEquiv.symm.toLinearMap

/-- The actual trace-normalized Casimir of one of the native graded Cartans. -/
abbrev nativeGradedCasimir (p : SignedPlaneIndex) : Module.End ℝ albertJordan.traceFree :=
  operatorCasimir (nativeAlbertRestrictedCartan (nativeGradedCartan p))

theorem nativeGradedCartan_isCartan (p : SignedPlaneIndex) :
    (nativeGradedCartan p).IsCartanSubalgebra :=
  albertGradingRealCartan_isCartan nativeGradingHom_isTernaryGrading p

theorem nativeGradedCartan_finrank (p : SignedPlaneIndex) :
    Module.finrank ℝ (nativeAlbertRestrictedCartan (nativeGradedCartan p)) = 4 := by
  have h : Function.Injective nativeAlbertRestrictDerivation :=
    albertJordan.restrictDerivation_injective.comp nativeAlbertDerivationSkewEquiv.injective
  exact (((nativeGradedCartan p).toSubmodule.equivMapOfInjective _ h).finrank_eq.symm).trans
    (albertGradingRealCartan_finrank nativeGradingHom_isTernaryGrading p)

theorem nativeGradedCartan_commutative (p : SignedPlaneIndex) :
    IsCommutativeSpace (nativeAlbertRestrictedCartan (nativeGradedCartan p)) := by
  rintro ⟨_, X, hX, rfl⟩ ⟨_, Y, hY, rfl⟩
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hz : ⁅X, Y⁆ = 0 :=
    (albertGradingRealCartan_selfCentralizing nativeGradingHom_isTernaryGrading p X).mpr hX Y hY
  have hh := congrArg (fun D : NativeAlbertDerivations => D.val x.val) hz
  change X.val (Y.val x.val) - Y.val (X.val x.val) = 0 at hh
  exact sub_eq_zero.mp hh

theorem nativeGradedCartan_fixedSpace (p : SignedPlaneIndex) :
    fixedSpace (nativeAlbertRestrictedCartan (nativeGradedCartan p)) = nativeGradedPlane p := by
  have h := congrArg (Submodule.map albertTraceEquiv.symm.toLinearMap)
    (nativeAlbertRestrictedCartan_fixed_eq (nativeGradedCartan p))
  rw [albertGradingRealCartan_fixedPlane nativeGradingHom_isTernaryGrading p] at h
  suffices hm : (albertTraceEquiv.symm.toLinearMap.comp albertTraceEquiv.toLinearMap) =
      LinearMap.id by
    simpa only [← Submodule.map_comp, hm, Submodule.map_id] using h
  exact LinearMap.ext albertTraceEquiv.symm_apply_apply

theorem nativeGradedCasimir_isSymmetric (p : SignedPlaneIndex) :
    (nativeGradedCasimir p).IsSymmetric := by
  let T := nativeAlbertRestrictedCartan (nativeGradedCartan p)
  let b := stdOrthonormalBasis ℝ T
  change (operatorCasimir T).IsSymmetric
  rw [operatorCasimir_eq_sum T b]
  intro x y
  simp only [LinearMap.neg_apply, LinearMap.sum_apply, inner_neg_left, inner_neg_right,
    sum_inner, inner_sum]
  apply congrArg (fun a : ℝ => -a)
  apply Finset.sum_congr rfl
  intro i _
  let D := (b i).val
  change ⟪D.val (D.val x), y⟫ = ⟪x, D.val (D.val y)⟫
  rw [D.property, D.property, neg_neg]

private theorem gradeCartan_map_eq {g : Glennie.CompactAutomorphism} {t u : Charge → Charge}
    (h : AlbertGradingCovariance g t u) (p : SignedPlaneIndex)
    (hp : u p.val.val = p.val.val) (hn : u (-p.val.val) = -p.val.val) :
    (nativeGradedCartan p).map (nativeAlbertLieAction g).toLieHom = nativeGradedCartan p := by
  let T := nativeGradedCartan p
  have hle : T.map (nativeAlbertLieAction g).toLieHom ≤ T := by
    rintro _ ⟨D, hD, rfl⟩
    exact h.maps_gradedCartan p hp hn hD
  have hr : Module.finrank ℝ (T.map (nativeAlbertLieAction g).toLieHom) =
      Module.finrank ℝ T :=
    ((nativeAlbertLieAction g).toLinearEquiv.submoduleMap T.toSubmodule).finrank_eq.symm
  exact LieSubalgebra.toSubmodule_injective (Submodule.eq_of_le_of_finrank_eq hle hr)

/-- A native symmetry stabilizing the reference grade pair commutes with its trace Casimir. -/
theorem nativeGradedCasimir_intertwines {g : Glennie.CompactAutomorphism} {t u : Charge → Charge}
    (h : AlbertGradingCovariance g t u) (p : SignedPlaneIndex)
    (hp : u p.val.val = p.val.val) (hn : u (-p.val.val) = -p.val.val)
    (x : albertJordan.traceFree) :
    nativeGradedCasimir p (((albertJordanAction g).traceAction albertJordan) x) =
      ((albertJordanAction g).traceAction albertJordan) (nativeGradedCasimir p x) := by
  have hc := nativeAlbertRestrictedCartan_casimir_map g (nativeGradedCartan p)
  rw [gradeCartan_map_eq h p hp hn] at hc
  let e := ((albertJordanAction g).traceAction albertJordan).toLinearEquiv
  have hx := LinearMap.congr_fun hc (e x)
  rw [LinearEquiv.conj_apply_apply] at hx
  change nativeGradedCasimir p (e x) = e (nativeGradedCasimir p (e.symm (e x))) at hx
  rw [e.symm_apply_apply] at hx
  exact hx

theorem nativeGradedCasimir_intertwines_charges (p : SignedPlaneIndex)
    (s : Charge) (x : albertJordan.traceFree) :
    nativeGradedCasimir p (((albertJordanAction (nativeChargeAutomorphism s)).traceAction albertJordan) x) =
      ((albertJordanAction (nativeChargeAutomorphism s)).traceAction albertJordan)
        (nativeGradedCasimir p x) := by
  have h : AlbertGradingCovariance (nativeChargeAutomorphism s) id id := by
    refine ⟨?_, fun _ _ => rfl⟩
    intro t x
    change Graded.nativeCharacterAction t (Graded.nativeCharacterAction s x) =
      Graded.nativeCharacterAction s (Graded.nativeCharacterAction t x)
    rw [← Graded.nativeCharacterAction_add, ← Graded.nativeCharacterAction_add, add_comm]
  exact nativeGradedCasimir_intertwines h p rfl rfl x

private theorem traceAction_eq_albertTracelessAction (g : Glennie.CompactAutomorphism)
    (x : albertJordan.traceFree) :
    albertTraceEquiv (((albertJordanAction g).traceAction albertJordan) x) =
      albertTracelessAction g (albertTraceEquiv x) :=
  Subtype.ext rfl

/-- A genuine compact Albert automorphism stabilizing the reference Cartan transits between
any two marked planes off its fixed plane. -/
theorem nativeGradedCasimir_offPoint_symmetry (p q r : SignedPlaneIndex)
    (hq : q ≠ p) (hr : r ≠ p) :
    ∃ e : albertJordan.traceFree ≃ₗᵢ[ℝ] albertJordan.traceFree,
      (∀ x, nativeGradedCasimir p (e x) = e (nativeGradedCasimir p x)) ∧
      (∀ x ∈ nativeGradedPlane q, e x ∈ nativeGradedPlane r) := by
  obtain ⟨A, hAp, hAq⟩ := sl_signedPlane_stabilizer_transitive p q r hq hr
  obtain ⟨F, hF, hf⟩ := codeLift_exists A
  obtain ⟨g, hg⟩ := exists_albertSignedLift (codeRelabeling A F hF) hf
  have h : AlbertGradingCovariance g (fun s => (A : ChargeMatrix)ᵀ *ᵥ s)
      (fun q => (A : ChargeMatrix) *ᵥ q) :=
    ⟨albertSignedLift_character A F hF g hg,
      fun s q => congrArg chargePhase (chargeDot_transpose_mulVec (A : ChargeMatrix) s q).symm⟩
  have hnp : (A : ChargeMatrix) *ᵥ (-p.val.val) = -p.val.val := by
    rw [Matrix.mulVec_neg, hAp]
  have hnq : (A : ChargeMatrix) *ᵥ (-q.val.val) = -r.val.val := by
    rw [Matrix.mulVec_neg, hAq]
  let e := (albertJordanAction g).traceAction albertJordan
  refine ⟨e, nativeGradedCasimir_intertwines h p hAp hnp, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hy := h.maps_pointPlane q r hAq hnq hx
  refine ⟨albertTracelessAction g x, hy, albertTraceEquiv.injective ?_⟩
  change albertTraceEquiv (albertTraceEquiv.symm (albertTracelessAction g x)) =
    albertTraceEquiv (((albertJordanAction g).traceAction albertJordan) (albertTraceEquiv.symm x))
  rw [albertTraceEquiv.apply_symm_apply, traceAction_eq_albertTracelessAction,
    albertTraceEquiv.apply_symm_apply]

end

end ThirteenPlanes.Cartan
