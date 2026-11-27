module

public import ThirteenPlanes.ClosedBlocks.CartanPieces
public import AcceptedRootAtomAdapter
public import NativeRecoveredCoordinates

@[expose] public section

set_option backward.privateInPublic true

/-! Extending the actual metric product of a closed complex block over the unit. -/

open scoped Matrix RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce AlbertSequential.NativeAnalysis

noncomputable section

private abbrev Hermitian := AlbertSequential.Hermitian3

private def hermitianScalar : Hermitian →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((Matrix.traceLinearMap (Fin 3) ℝ ℂ).comp
    (selfAdjoint.submodule ℝ ComplexMatrix3).subtype)

private def hermitianCenter : Hermitian →ₗ[ℝ] TracelessHermitian3 where
  toFun X := TracelessHermitian3.ofMatrix (traceFreePart X.val)
    (traceFreePart_hermitian (show X.val.IsHermitian from X.property))
    (trace_traceFreePart _)
  map_add' X Y := by
    apply TracelessHermitian3.toMatrix_injective
    change traceFreePart (X.val + Y.val) = _
    simpa only [TracelessHermitian3.toMatrix_ofMatrix, map_add] using traceFreePart_add X.val Y.val
  map_smul' t X := by
    apply TracelessHermitian3.toMatrix_injective
    change traceFreePart ((t : ℂ) • X.val) = _
    rw [map_smul, RingHom.id_apply]
    exact traceFreePart_smul (t : ℂ) X.val

private def hermitianInclusion : TracelessHermitian3 →ₗ[ℝ] Hermitian where
  toFun X := ⟨X.toMatrix, X.isHermitian.eq⟩
  map_add' X Y := Subtype.ext (TracelessHermitian3.toMatrix.map_add X Y)
  map_smul' t X := Subtype.ext (TracelessHermitian3.toMatrix.map_smul t X)

private theorem scalar_zero_centered (X : TracelessHermitian3) :
    hermitianScalar (hermitianInclusion X) = 0 := by
  change (Matrix.trace X.toMatrix).re = 0
  simp

private theorem center_centered (X : TracelessHermitian3) :
    hermitianCenter (hermitianInclusion X) = X := by
  apply TracelessHermitian3.toMatrix_injective
  change traceFreePart X.toMatrix = X.toMatrix
  simp [traceFreePart]

private theorem matrix_split (X : Hermitian) :
    X.val = (hermitianScalar X / 3) • (1 : ComplexMatrix3) + (hermitianCenter X).toMatrix := by
  change X.val = (hermitianScalar X / 3) • (1 : ComplexMatrix3) + traceFreePart X.val
  unfold traceFreePart
  rw [hermitian_trace_eq_real (show X.val.IsHermitian from X.property)]
  have hc : hermitianScalar X = (Matrix.trace X.val).re := rfl
  rw [hc, ← Complex.ofReal_ofNat, ← Complex.ofReal_div]
  change X.val = ((↑((Matrix.trace X.val).re / 3) : ℂ) • (1 : ComplexMatrix3)) +
    (X.val - ((↑((Matrix.trace X.val).re / 3) : ℂ) • (1 : ComplexMatrix3)))
  abel

private def hermitianProduct (X Y : Hermitian) : Hermitian :=
  ⟨symmetricMatrixProduct X.val Y.val,
    (symmetricMatrixProduct_hermitian (show X.val.IsHermitian from X.property)
      (show Y.val.IsHermitian from Y.property)).eq⟩

private theorem hermitianProduct_matrix (X Y : Hermitian) :
    (hermitianProduct X Y).val =
      (1 / 2 : ℝ) • (X.val * Y.val + Y.val * X.val) := by
  change (1 / 2 : ℂ) • (X.val * Y.val + Y.val * X.val) =
    (1 / 2 : ℝ) • (X.val * Y.val + Y.val * X.val)
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div]
  rfl

private theorem product_split (X Y : Hermitian) :
    (hermitianProduct X Y).val =
      (hermitianScalar X / 3 * (hermitianScalar Y / 3)) • (1 : ComplexMatrix3) +
      (hermitianScalar X / 3) • (hermitianCenter Y).toMatrix +
      (hermitianScalar Y / 3) • (hermitianCenter X).toMatrix +
      symmetricMatrixProduct (hermitianCenter X).toMatrix (hermitianCenter Y).toMatrix := by
  unfold hermitianProduct
  change symmetricMatrixProduct X.val Y.val = _
  rw [matrix_split X, matrix_split Y]
  simp only [symmetricMatrixProduct, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_comm (1 / 2 : ℂ), smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

private theorem trace_symmetricMatrixProduct (A B : ComplexMatrix3) :
    (Matrix.trace (symmetricMatrixProduct A B)).re = tracePairing A B := by
  rw [symmetricMatrixProduct, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_comm B A,
    ← two_smul ℂ, smul_smul]
  norm_num [tracePairing]

private theorem hermitianScalar_product (X Y : Hermitian) :
    hermitianScalar (hermitianProduct X Y) / 3 =
      hermitianScalar X / 3 * (hermitianScalar Y / 3) +
      ⟪hermitianCenter X, hermitianCenter Y⟫ / 3 := by
  change (Matrix.trace (hermitianProduct X Y).val).re / 3 = _
  rw [product_split]
  simp only [Matrix.trace_add, Matrix.trace_smul, TracelessHermitian3.trace_eq_zero, smul_zero,
    add_zero, trace_one_matrix3, Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  norm_num
  rw [trace_symmetricMatrixProduct]
  change _ = _ + inner ℝ (hermitianCenter X) (hermitianCenter Y) / 3
  rw [TracelessHermitian3.inner_eq_tracePairing]
  ring

private theorem hermitianCenter_product (X Y : Hermitian) :
    hermitianCenter (hermitianProduct X Y) =
      (hermitianScalar X / 3) • hermitianCenter Y +
      (hermitianScalar Y / 3) • hermitianCenter X +
      TracelessHermitian3.jordan (hermitianCenter X) (hermitianCenter Y) := by
  apply TracelessHermitian3.toMatrix_injective
  change traceFreePart (hermitianProduct X Y).val = _
  rw [product_split]
  simp only [traceFreePart_add, map_add, map_smul, TracelessHermitian3.toMatrix_jordan]
  have ht (t : ℝ) : traceFreePart (t • (1 : ComplexMatrix3)) = 0 := by
    simp only [traceFreePart, Matrix.trace_smul, trace_one_matrix3, smul_eq_mul,
      show (t • (1 : ComplexMatrix3)) = (t : ℂ) • (1 : ComplexMatrix3) by rfl]
    rw [show (t : ℂ) * 3 / 3 = t by ring, sub_self]
  rw [ht, zero_add]
  have hc (t : ℝ) (Z : TracelessHermitian3) :
      traceFreePart (t • Z.toMatrix) = t • Z.toMatrix := by
    simp [traceFreePart, Matrix.trace_smul]
  rw [hc, hc]

private def unitCoordinate : ℝ →ₗ[ℝ] Glennie.Albert :=
  (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (1 : Glennie.Albert)

private def hermitianScalarThird : Hermitian →ₗ[ℝ] ℝ := (3 : ℝ)⁻¹ • hermitianScalar

private def embedCenter {U : Submodule ℝ NativeTraceless}
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3) : TracelessHermitian3 →ₗ[ℝ] Glennie.Albert :=
  Glennie.traceLinear.ker.subtype.comp (U.subtype.comp I.symm.toLinearMap)

private def embedHermitian {U : Submodule ℝ NativeTraceless}
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3) : Hermitian →ₗ[ℝ] Glennie.Albert :=
  unitCoordinate.comp hermitianScalarThird + (embedCenter I).comp hermitianCenter

private theorem embedHermitian_apply {U : Submodule ℝ NativeTraceless}
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3) (X : Hermitian) :
    embedHermitian I X = (hermitianScalar X / 3) • (1 : Glennie.Albert) +
      embedCenter I (hermitianCenter X) := by
  change ((3 : ℝ)⁻¹ * hermitianScalar X) • (1 : Glennie.Albert) + _ = _
  rw [mul_comm, ← div_eq_mul_inv, LinearMap.comp_apply]

private theorem embedCenter_trace {U : Submodule ℝ NativeTraceless}
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3) (X : TracelessHermitian3) :
    Glennie.trace (embedCenter I X) = 0 :=
  nativeTraceless_trace (I.symm X : U)

private theorem embedHermitian_trace {U : Submodule ℝ NativeTraceless}
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3) (X : Hermitian) :
    Glennie.trace (embedHermitian I X) = hermitianScalar X := by
  rw [embedHermitian_apply, Glennie.trace_add, Glennie.trace_smul, embedCenter_trace]
  have h : Glennie.trace (1 : Glennie.Albert) = 3 := by norm_num
  rw [h, add_zero]
  ring

private theorem embedHermitian_injective {U : Submodule ℝ NativeTraceless}
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3) : Function.Injective (embedHermitian I) := by
  intro X Y h
  have hs := congrArg Glennie.trace h
  simp only [embedHermitian_trace] at hs
  rw [embedHermitian_apply, embedHermitian_apply, hs, add_right_inj] at h
  have hc := I.symm.injective (Subtype.ext (Subtype.ext h))
  apply Subtype.ext
  rw [matrix_split X, matrix_split Y, hs, hc]

set_option maxHeartbeats 500000 in
private theorem embedCenter_product {U : Submodule ℝ NativeTraceless}
    (closed : IsClosedPiece nativeEqualCubic U)
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3)
    (hI : nativeEqualCubic.pullback U.subtype = matrixEqualCubic.pullback (W := ↥U) I.toLinearMap)
    (X Y : TracelessHermitian3) :
    Glennie.jordan (embedCenter I X) (embedCenter I Y) =
      (⟪X, Y⟫ / 3) • (1 : Glennie.Albert) + embedCenter I (TracelessHermitian3.jordan X Y) := by
  let x := I.symm X
  let y := I.symm Y
  have hc : I ((nativeEqualCubic.pullback (W := ↥U) U.subtype).L x y) =
      TracelessHermitian3.jordan X Y := by
    have hxy := Peirce.pullback_intertwines_product (h := nativeEqualCubic.pullback (W := ↥U) U.subtype)
      (k := matrixEqualCubic) I hI x y
    change _ = TracelessHermitian3.jordan (I (I.symm X)) (I (I.symm Y)) at hxy
    simpa only [I.apply_symm_apply] using hxy
  have he := congrArg (fun z : TracelessHermitian3 => ((I.symm z : U) : NativeTraceless)) hc
  change ((I.symm (I ((nativeEqualCubic.pullback U.subtype).L x y)) : U) : NativeTraceless) =
    ((I.symm (TracelessHermitian3.jordan X Y) : U) : NativeTraceless) at he
  rw [I.symm_apply_apply, closedSubspace_restriction_product closed] at he
  let Z := Glennie.jordan (embedCenter I X) (embedCenter I Y)
  have ht : Glennie.trace Z = inner ℝ X Y := by
    change Glennie.inner (embedCenter I X) (embedCenter I Y) = _
    rw [← Glennie.hilbert_inner_eq_native]
    change inner ℝ (I.symm X : U) (I.symm Y : U) = inner ℝ X Y
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      ← I.symm.map_add, I.symm.norm_map, I.symm.norm_map, I.symm.norm_map]
  have he' : Glennie.traceless Z = embedCenter I (TracelessHermitian3.jordan X Y) :=
    congrArg (fun z : NativeTraceless => z.val) he
  rw [Glennie.traceless, ht] at he'
  change Z = ((inner ℝ X Y) / 3) • (1 : Glennie.Albert) + _
  rw [← he']
  abel

private theorem embedHermitian_product {U : Submodule ℝ NativeTraceless}
    (closed : IsClosedPiece nativeEqualCubic U)
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3)
    (hI : nativeEqualCubic.pullback U.subtype = matrixEqualCubic.pullback (W := ↥U) I.toLinearMap)
    (X Y : Hermitian) :
    embedHermitian I (hermitianProduct X Y) =
      Glennie.jordan (embedHermitian I X) (embedHermitian I Y) := by
  rw [embedHermitian_apply, embedHermitian_apply, embedHermitian_apply, hermitianScalar_product,
    hermitianCenter_product, map_add, map_add, map_smul, map_smul, add_smul]
  simp only [Glennie.jordan_add_left, Glennie.jordan_add_right, Glennie.jordan_smul_left,
    Glennie.jordan_smul_right, Glennie.jordan_unit_left, Glennie.jordan_unit_right, smul_add, smul_smul, mul_comm (hermitianScalar Y / 3),
    embedCenter_product closed I hI]
  abel

/-- Restore the unit to an actual product-preserving octet isometry and obtain a
native complex window whose traceless points are exactly the original block. -/
theorem complexWindow_of_closedBlock {U : Submodule ℝ NativeTraceless}
    (closed : IsClosedPiece nativeEqualCubic U)
    (I : U ≃ₗᵢ[ℝ] TracelessHermitian3)
    (hI : nativeEqualCubic.pullback U.subtype = matrixEqualCubic.pullback (W := ↥U) I.toLinearMap) :
    ∃ W : AlbertSequential.ComplexWindow, ∀ x : NativeTraceless,
      W.Contains (recoveredCoordinateEquiv.symm x.val) ↔ x ∈ U := by
  let E := recoveredCoordinateEquiv
  let W : AlbertSequential.ComplexWindow :=
    { embedding := E.symm.toLinearMap.comp (embedHermitian I)
      injective := E.symm.injective.comp (embedHermitian_injective I)
      unit := by
        change E.symm (embedHermitian I (1 : Hermitian)) = _
        apply E.injective
        rw [E.apply_symm_apply, recoveredCoordinateEquiv_unit, embedHermitian_apply]
        have hs : hermitianScalar (1 : Hermitian) = 3 := by
          change (Matrix.trace (1 : ComplexMatrix3)).re = 3
          simp
        have hc : hermitianCenter (1 : Hermitian) = 0 := by
          apply TracelessHermitian3.toMatrix_injective
          change traceFreePart (1 : ComplexMatrix3) = 0
          norm_num [traceFreePart]
        rw [hs, hc, map_zero, add_zero, div_self (by norm_num), one_smul]
      product_closed := fun X Y => ⟨hermitianProduct X Y, hermitianProduct_matrix X Y⟩
      preserves_product := by
        intro X Y Z hZ
        have he : Z = hermitianProduct X Y := Subtype.ext (hZ.trans (hermitianProduct_matrix X Y).symm)
        subst Z
        apply E.injective
        change E (E.symm (embedHermitian I (hermitianProduct X Y))) =
          E (AlbertSequential.jordanMul (E.symm (embedHermitian I X)) (E.symm (embedHermitian I Y)))
        rw [recoveredCoordinateEquiv_jordanMul, E.apply_symm_apply, E.apply_symm_apply,
          E.apply_symm_apply, embedHermitian_product closed I hI]
      preserves_trace := by
        intro X
        change AlbertSequential.albertTrace (E.symm (embedHermitian I X)) = _
        rw [← recoveredCoordinateEquiv_trace, E.apply_symm_apply, embedHermitian_trace]
        rfl }
  refine ⟨W, fun x => ?_⟩
  constructor
  · rintro ⟨X, hX⟩
    have h : embedHermitian I X = x.val := E.symm.injective hX
    have ht := congrArg Glennie.trace h
    rw [embedHermitian_trace, nativeTraceless_trace] at ht
    rw [embedHermitian_apply, ht, zero_div, zero_smul, zero_add] at h
    have hx : ((I.symm (hermitianCenter X) : U) : NativeTraceless) = x := Subtype.ext h
    rw [← hx]
    exact (I.symm (hermitianCenter X)).property
  · intro hx
    refine ⟨hermitianInclusion (I ⟨x, hx⟩), ?_⟩
    change E.symm (embedHermitian I (hermitianInclusion (I ⟨x, hx⟩))) = E.symm x.val
    rw [embedHermitian_apply, scalar_zero_centered, center_centered, zero_div, zero_smul, zero_add]
    exact congrArg (fun z : U => E.symm z.val.val) (I.symm_apply_apply ⟨x, hx⟩)

end

end ThirteenPlanes.ClosedBlocks
