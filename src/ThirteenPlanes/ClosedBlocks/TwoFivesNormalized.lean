module

public import ThirteenPlanes.ClosedBlocks.NativeRotation
public import ThirteenPlanes.ClosedBlocks.OctetComplement
public import ThirteenPlanes.ClosedBlocks.CartanPieces

@[expose] public section

set_option backward.privateInPublic true

/-! The two isometric slot maps and rotation compression in the standard real chart. -/

open scoped RealInnerProductSpace ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics AlbertSequential AlbertSequential.NativeAnalysis

noncomputable section

local notation "Oct" => AlbertSequential.Octonion

private def octonionRealLinear : Oct →ₗ[ℝ] ℝ where
  toFun a := a.1.re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private abbrev Imaginary := octonionRealLinear.ker

private instance : FiniteDimensional ℝ Oct :=
  inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))

private theorem imaginary_finrank : Module.finrank ℝ Imaginary = 7 := by
  have hr : Function.Surjective octonionRealLinear := fun r => ⟨octonionScalar r, rfl⟩
  have hh := octonionRealLinear.finrank_range_add_finrank_ker
  have hd : Module.finrank ℝ Oct = 8 := by
    change Module.finrank ℝ (Quaternion ℝ × Quaternion ℝ) = 8
    rw [Module.finrank_prod, Quaternion.finrank_eq_four]
  rw [LinearMap.range_eq_top.mpr hr, finrank_top, Module.finrank_self, hd] at hh
  change 1 + Module.finrank ℝ Imaginary = 8 at hh
  omega

private def slot (i : Fin 3) : NativeTraceless →ₗ[ℝ] Oct :=
  (derivationSlotCoord i).comp nativeCoordinates

private theorem coordinates_inner (x y : NativeTraceless) :
    ⟪x, y⟫ = AlbertSequential.tracePairing (nativeCoordinates x) (nativeCoordinates y) := by
  change inner ℝ x.val y.val = _
  rw [Glennie.hilbert_inner_eq_native, ← recoveredCoordinateEquiv_tracePairing]
  change _ = Glennie.inner (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm x.val))
    (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm y.val))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private theorem coordinates_square (x : NativeTraceless) :
    nativeCoordinates (nativeEqualCubic.L x x) =
      let X := nativeCoordinates x
      let J := jordanMul X X
      J - (albertTrace J / 3) • albertUnit := by
  dsimp only
  apply recoveredCoordinateEquiv.injective
  change recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm (Glennie.traceless
    (Glennie.jordan x.val x.val))) = _
  rw [LinearEquiv.apply_symm_apply, map_sub, map_smul, recoveredCoordinateEquiv_unit,
    ← recoveredCoordinateEquiv_trace, recoveredCoordinateEquiv_jordanMul]
  change _ = Glennie.jordan (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm x.val))
      (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm x.val)) -
    (Glennie.trace (Glennie.jordan (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm x.val))
      (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm x.val))) / 3) • (1 : Glennie.Albert)
  simp only [LinearEquiv.apply_symm_apply, Glennie.traceless]

variable {S : Submodule ℝ NativeTraceless}

private theorem square_real_window_components (x : S)
    (closed : IsClosedPiece nativeEqualCubic S)
    (hd : ∀ (x : S) (i : Fin 3), (nativeCoordinates x.val).1 i = 0)
    (hr : ∀ (x : S) (i : Fin 3), ((nativeCoordinates x.val).2 i).1.re = 0) :
    let X := nativeCoordinates x.val
    (∀ i j : Fin 3, (jordanMul X X).1 i = (jordanMul X X).1 j) ∧
      (∀ i : Fin 3, ((jordanMul X X).2 i).1.re = 0) := by
  let X := nativeCoordinates x.val
  let J := jordanMul X X
  let t := albertTrace J / 3
  let y : S := ⟨nativeEqualCubic.L x.val x.val, closed x.property x.property⟩
  have hy : nativeCoordinates y.val = J - t • albertUnit := coordinates_square x.val
  have ho (i : Fin 3) : J.1 i = t := by
    have h := hd y i
    rw [hy] at h
    change J.1 i - t * 1 = 0 at h
    linarith
  refine ⟨fun i j => (ho i).trans (ho j).symm, fun i => ?_⟩
  have h := hr y i
  rw [hy] at h
  change (J.2 i - t • (0 : Oct)).1.re = 0 at h
  simpa only [smul_zero, sub_zero] using h

private theorem equal_slot_norms (x : S)
    (closed : IsClosedPiece nativeEqualCubic S)
    (hd : ∀ (x : S) (i : Fin 3), (nativeCoordinates x.val).1 i = 0)
    (hr : ∀ (x : S) (i : Fin 3), ((nativeCoordinates x.val).2 i).1.re = 0) :
    ∀ i : Fin 3, 6 * octNormSq (slot i x.val) = ‖x‖ ^ 2 := by
  let X := nativeCoordinates x.val
  have hh := (square_real_window_components x closed hd hr).1
  have h0 := hh 0 1
  have h1 := hh 0 2
  change (jordanMul X X).1 0 = (jordanMul X X).1 1 at h0
  change (jordanMul X X).1 0 = (jordanMul X X).1 2 at h1
  have hd' (i : Fin 3) : X.1 i = 0 := hd x i
  simp only [jordanMul_diag_0, jordanMul_diag_1, jordanMul_diag_2, hd', zero_mul, octDot_self,
    zero_add] at h0 h1
  have hn : ‖x‖ ^ 2 = 2 * (octNormSq (X.2 0) + octNormSq (X.2 1) + octNormSq (X.2 2)) := by
    change ‖x.val‖ ^ 2 = _
    rw [← real_inner_self_eq_norm_sq x.val]
    rw [coordinates_inner, tracePairing_eq_coords]
    change (X.1 0 * X.1 0 + X.1 1 * X.1 1 + X.1 2 * X.1 2) + _ = _
    simp [hd', octDot_self, X]
  intro i
  change 6 * octNormSq (X.2 i) = ‖x‖ ^ 2
  fin_cases i
  · change 6 * octNormSq (X.2 0) = ‖x‖ ^ 2
    linarith only [h0, h1, hn]
  · change 6 * octNormSq (X.2 1) = ‖x‖ ^ 2
    linarith only [h0, h1, hn]
  · change 6 * octNormSq (X.2 2) = ‖x‖ ^ 2
    linarith only [h0, h1, hn]

private theorem inner_slots12 (x : S)
    (closed : IsClosedPiece nativeEqualCubic S)
    (hd : ∀ (x : S) (i : Fin 3), (nativeCoordinates x.val).1 i = 0)
    (hr : ∀ (x : S) (i : Fin 3), ((nativeCoordinates x.val).2 i).1.re = 0) :
    octDot (slot 1 x.val) (slot 2 x.val) = 0 := by
  let X := nativeCoordinates x.val
  have ho := (square_real_window_components x closed hd hr).2 0
  change ((jordanMul X X).2 0).1.re = 0 at ho
  have h := (nativeSquare_offDiagonal_of_zero_diagonal X (hd x) (hr x)).1
  rw [h] at ho
  change - (octonionMul (X.2 1) (X.2 2)).1.re = 0 at ho
  change octDot (X.2 1) (X.2 2) = 0
  rw [octDot, nativeOctonion_conj_eq_neg_of_real_zero (hr x 2),
    octonionMul_neg_right]
  exact ho

private def normalizedSlot (i : Fin 3)
    (closed : IsClosedPiece nativeEqualCubic S)
    (hd : ∀ (x : S) (i : Fin 3), (nativeCoordinates x.val).1 i = 0)
    (hr : ∀ (x : S) (i : Fin 3), ((nativeCoordinates x.val).2 i).1.re = 0) :
    S →ₗᵢ[ℝ] Imaginary where
  toLinearMap := ((Real.sqrt 6 • slot i).comp S.subtype).codRestrict _ fun x => by
    change octonionRealLinear (Real.sqrt 6 • slot i x.val) = 0
    rw [map_smul, show octonionRealLinear (slot i x.val) = 0 from hr x i, smul_zero]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖Real.sqrt 6 • slot i x.val‖ ^ 2 = ‖x‖ ^ 2
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by norm_num), MarkedPlane.nativeOctonion_norm_sq]
    exact equal_slot_norms x closed hd hr i

private theorem normalizedSlot_diagonal_orth
    (closed : IsClosedPiece nativeEqualCubic S)
    (hd : ∀ (x : S) (i : Fin 3), (nativeCoordinates x.val).1 i = 0)
    (hr : ∀ (x : S) (i : Fin 3), ((nativeCoordinates x.val).2 i).1.re = 0)
    (x : S) :
    ⟪normalizedSlot 1 closed hd hr x, normalizedSlot 2 closed hd hr x⟫ = 0 := by
  change ⟪Real.sqrt 6 • slot 1 x.val, Real.sqrt 6 • slot 2 x.val⟫ = 0
  rw [real_inner_smul_left, real_inner_smul_right, MarkedPlane.nativeOctonion_inner,
    inner_slots12 x closed hd hr, mul_zero, mul_zero]

/-- Compression to a closed block in the standard real orthogonal complement is
two-thirds of the overlap of its second and third slot isometries. -/
theorem normalizedRealComplement_compressedRotation
    (closed : IsClosedPiece nativeEqualCubic S)
    (hd : ∀ (x : S) (i : Fin 3), (nativeCoordinates x.val).1 i = 0)
    (hr : ∀ (x : S) (i : Fin 3), ((nativeCoordinates x.val).2 i).1.re = 0) :
    ∃ (F G : S →ₗᵢ[ℝ] Imaginary),
      compressToBlock S nativeRotation = (2 / 3 : ℝ) • ((LinearMap.adjoint (𝕜 := ℝ) (E := ↥S) (F := ↥Imaginary) F.toLinearMap).comp G.toLinearMap) := by
  let F := normalizedSlot 1 closed hd hr
  let G := normalizedSlot 2 closed hd hr
  refine ⟨F, G, ?_⟩
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [inner_compressToBlock_left, coordinates_inner, tracePairing_eq_coords]
  obtain ⟨h0, h1, h2⟩ := nativeRotation_upper_slots x.val (hd x)
  simp only [hd, mul_zero, add_zero, h0, h1, h2, octDot_zero_left, zero_add]
  have hboth : ⟪F x, G y⟫ = -⟪G x, F y⟫ := by
    have hh := normalizedSlot_diagonal_orth closed hd hr (x + y)
    change ⟪F (x + y), G (x + y)⟫ = 0 at hh
    simp only [map_add, inner_add_left, inner_add_right,
      show ⟪F x, G x⟫ = 0 from normalizedSlot_diagonal_orth closed hd hr x,
      show ⟪F y, G y⟫ = 0 from normalizedSlot_diagonal_orth closed hd hr y,
      add_zero, zero_add] at hh
    rw [real_inner_comm (G x) (F y)] at hh
    linarith only [hh]
  have oct_scale (x y : S) : ⟪F x, G y⟫ =
      6 * octDot (slot 1 x.val) (slot 2 y.val) := by
    change ⟪Real.sqrt 6 • slot 1 x.val, Real.sqrt 6 • slot 2 y.val⟫ = _
    rw [real_inner_smul_left, real_inner_smul_right, MarkedPlane.nativeOctonion_inner, ← mul_assoc,
      ← pow_two, Real.sq_sqrt (by norm_num)]
  have oct_scale' (x y : S) : ⟪G x, F y⟫ =
      6 * octDot (slot 2 x.val) (slot 1 y.val) := by
    rw [real_inner_comm, oct_scale, octDot_comm]
  rw [inner_scaledOverlap (V := ↥S) (W := ↥Imaginary) F.toLinearMap G.toLinearMap]
  change 2 * (octDot (slot 2 x.val) (slot 1 y.val) + octDot (-(slot 1 x.val)) (slot 2 y.val)) =
    (2 / 3 : ℝ) * ⟪G x, F y⟫
  rw [octDot_neg_left, oct_scale']
  rw [oct_scale, oct_scale'] at hboth
  linarith only [hboth]


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
/-- The five-dimensional Gram eigenspace obstruction once the real Cartan
derivation bound is supplied on its actual traceless carrier. -/
theorem noFiveInStandardRealComplement_of_derivation_bound
    (closed : IsClosedPiece nativeEqualCubic S)
    (hd : ∀ (x : S) (i : Fin 3), (nativeCoordinates x.val).1 i = 0)
    (hr : ∀ (x : S) (i : Fin 3), ((nativeCoordinates x.val).2 i).1.re = 0)
    (harmonic : (nativeEqualCubic.pullback (W := ↥S) S.subtype).TraceFree)
    (h5 : Module.finrank ℝ S = 5)
    (derivation_bound : ∀ D : Module.End ℝ Peirce.RealTracelessSymmetric3,
      (∀ x y, D (Peirce.realCartanCubic.L x y) =
        Peirce.realCartanCubic.L (D x) y + Peirce.realCartanCubic.L x (D y)) →
      (∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫) →
      ∀ t : ℝ, 0 < t →
        Module.finrank ℝ (LinearMap.ker ((LinearMap.adjoint (𝕜 := ℝ) (E := ↥Peirce.RealTracelessSymmetric3)
          (F := ↥Peirce.RealTracelessSymmetric3) D).comp D - t • LinearMap.id)) ≤ 2) :
    False := by
  let E := compressToBlock S nativeRotation
  let V := Peirce.RealTracelessSymmetric3
  have nr : IsRound nativeEqualCubic (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [nativeEqualCubic_squareLaw x]
    ring
  obtain ⟨I, hI⟩ := harmonic_round_five_cartan
    (closedSubspace_restriction_isRound nr closed) harmonic h5
  obtain ⟨F, G, hE⟩ := normalizedRealComplement_compressedRotation closed hd hr
  let F' : V →ₗᵢ[ℝ] Imaginary := F.comp I.symm.toLinearIsometry
  let G' : V →ₗᵢ[ℝ] Imaginary := G.comp I.symm.toLinearIsometry
  let D : Module.End ℝ V := I.toLinearEquiv.conj E
  have hs : Real.sqrt (1 / 6) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 6)).ne'
  have hder (x y : S) :
      E ((nativeEqualCubic.pullback (W := ↥S) S.subtype).L x y) =
        (nativeEqualCubic.pullback (W := ↥S) S.subtype).L (E x) y +
          (nativeEqualCubic.pullback (W := ↥S) S.subtype).L x (E y) :=
    compressToBlock_derivation closed nativeRotation_derivation x y
  obtain ⟨hDder, hDskew⟩ :=
    @skewDerivation_conj_of_smul_pullback ↥S inferInstance (Submodule.innerProductSpace S) inferInstance
      ↥Peirce.RealTracelessSymmetric3 inferInstance
      (inferInstance : InnerProductSpace ℝ ↥Peirce.RealTracelessSymmetric3) inferInstance
      I _ _ _ hs hI E hder (compressToBlock_skew nativeRotation_skew)
  have heq : D = (2 / 3 : ℝ) •
      ((LinearMap.adjoint (𝕜 := ℝ) (E := ↥V) (F := ↥Imaginary) F'.toLinearMap).comp G'.toLinearMap) := by
    have hc := congrArg I.toLinearEquiv.conj hE
    have hc' := @scaledOverlap_conj ↥S ↥Imaginary
      inferInstance (Submodule.innerProductSpace S) inferInstance
      inferInstance (Submodule.innerProductSpace Imaginary) inferInstance
      ↥Peirce.RealTracelessSymmetric3 inferInstance
      (inferInstance : InnerProductSpace ℝ ↥Peirce.RealTracelessSymmetric3) inferInstance I F G (2 / 3)
    exact hc.trans hc'
  have hsmall := derivation_bound D hDder hDskew ((2 / 3 : ℝ)^2) (by norm_num)
  have hlarge := @scaledOverlap_eigenspace_finrank ↥Peirce.RealTracelessSymmetric3 ↥Imaginary
    inferInstance (inferInstance : InnerProductSpace ℝ ↥Peirce.RealTracelessSymmetric3) inferInstance
    inferInstance (Submodule.innerProductSpace Imaginary) inferInstance F' G' (2 / 3 : ℝ)
  dsimp only at hlarge
  rw [← heq, imaginary_finrank] at hlarge
  have hV : Module.finrank ℝ Peirce.RealTracelessSymmetric3 = 5 :=
    I.toLinearEquiv.finrank_eq.symm.trans h5
  rw [hV] at hlarge
  omega

end

end ThirteenPlanes.ClosedBlocks
