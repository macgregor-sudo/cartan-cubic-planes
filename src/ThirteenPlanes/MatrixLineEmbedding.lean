module

public import ThirteenPlanes.SignedTits
public import ThirteenPlanes.FourPlanes

@[expose] public section

set_option backward.privateInPublic true

open scoped Matrix RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes

noncomputable section

private def matrixLineValue (x : TracelessHermitian3) : Tits.CompactTitsTraceless :=
  Tits.CompactTitsTraceless.ofMatrices (TracelessHermitian3.toMatrix x) 0
    (TracelessHermitian3.isHermitian x)
    (by rw [Tits.trace3_eq_matrixTrace, TracelessHermitian3.trace_eq_zero])

@[simp] private theorem matrixLineValue_coordinates (x : TracelessHermitian3) :
    Tits.CompactTitsTraceless.coordinates (matrixLineValue x) =
      (TracelessHermitian3.toMatrix x, 0, 0) := by
  simp [matrixLineValue]

private theorem compactCoordinates_injective :
    Function.Injective Tits.CompactTitsTraceless.coordinates :=
  fun _ _ h => Subtype.ext (Tits.CompactTits.ext h)

private def matrixLineLinear : TracelessHermitian3 →ₗ[ℝ] Tits.CompactTitsTraceless where
  toFun := matrixLineValue
  map_add' x y := compactCoordinates_injective (by
    simp only [matrixLineValue_coordinates, map_add, Prod.mk_add_mk, add_zero])
  map_smul' r x := compactCoordinates_injective (by
    simp only [matrixLineValue_coordinates, map_smul, Prod.smul_mk, smul_zero, RingHom.id_apply])

/-- The traceless Hermitian matrix fields are isometrically embedded in the first Tits component. -/
def matrixLineTits : TracelessHermitian3 →ₗᵢ[ℝ] Tits.CompactTitsTraceless where
  toLinearMap := matrixLineLinear
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(matrixLineValue x).val‖ ^ 2 = ‖x‖ ^ 2
    rw [Tits.CompactTits.norm_sq_eq_tracePairing, TracelessHermitian3.norm_sq_eq_tracePairing]
    have h : Tits.CompactTits.coordinates (matrixLineValue x).val =
        (TracelessHermitian3.toMatrix x, 0, 0) := matrixLineValue_coordinates x
    simp [Tits.CompactTits.tracePairing, tracePairing, h]

@[simp] theorem matrixLineTits_coordinates (x : TracelessHermitian3) :
    Tits.CompactTitsTraceless.coordinates (matrixLineTits x) =
      (TracelessHermitian3.toMatrix x, 0, 0) := matrixLineValue_coordinates x

/-- The representative signed line, with all nonzero grades of third charge zero. -/
def matrixLineEmbed : TracelessHermitian3 →ₗᵢ[ℝ] SignedField :=
  gradedTitsEquiv.symm.toLinearIsometry.comp matrixLineTits

@[simp] theorem gradedTitsEquiv_matrixLineEmbed (x : TracelessHermitian3) :
    gradedTitsEquiv (matrixLineEmbed x) = matrixLineTits x :=
  gradedTitsEquiv.apply_symm_apply _

theorem matrixLineEmbed_coordinates (x : TracelessHermitian3) :
    gradedTitsCoordinates (signedExtend (matrixLineEmbed x)) =
      (TracelessHermitian3.toMatrix x, 0, 0) := by
  rw [← gradedTitsEquiv_coordinates, gradedTitsEquiv_matrixLineEmbed, matrixLineTits_coordinates]

private theorem firstComponent_off (A : Mat3 ℂ) (k : ZMod 3) (hk : k ≠ 0) :
    titsComponent (A, (0, 0)) k = 0 := by
  fin_cases k
  · exact (hk rfl).elim
  · rfl
  · rfl

theorem matrixLineEmbed_off_charge (x : TracelessHermitian3) (q : NonzeroCharge)
    (hq : q.val 2 ≠ 0) : signedCoordinates (matrixLineEmbed x) q = 0 := by
  have h := congrArg (fun z => titsComponent z (q.val 2)) (matrixLineEmbed_coordinates x)
  change titsComponent (gradedTitsCoordinates (signedExtend (matrixLineEmbed x))) (q.val 2) =
      titsComponent (TracelessHermitian3.toMatrix x, (0, 0)) (q.val 2) at h
  rw [titsComponent_gradedTitsCoordinates, firstComponent_off _ _ hq] at h
  have hh : weylSynthesis (fun v => signedExtend (matrixLineEmbed x) (chargeFrom v (q.val 2))) =
      weylSynthesis 0 := by
    rw [map_zero]
    exact h
  have he := congrFun (weylSynthesis_injective hh) (q.val 0, q.val 1)
  simpa only [chargeFrom_components, Pi.zero_apply, signedExtend_nonzero] using he

private theorem matrixLineTits_square (x : TracelessHermitian3) :
    Tits.CompactTitsTraceless.square (matrixLineTits x) =
      matrixLineTits (TracelessHermitian3.square x) := by
  apply compactCoordinates_injective
  rw [Tits.CompactTitsTraceless.coordinates_square, matrixLineTits_coordinates,
    matrixLineTits_coordinates, TracelessHermitian3.toMatrix_square]
  let A := TracelessHermitian3.toMatrix x
  have hadj : adjugate3 (0 : Mat3 ℂ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjugate3]
  have hSq : firstTitsSquare ((A, 0, 0) : FirstTits ℂ) = (A * A, 0, 0) := by
    simp [firstTitsSquare, trace3, hadj]
  have hX : Tits.CompactTits.coordinates (matrixLineTits x).val = (A, 0, 0) :=
    matrixLineTits_coordinates x
  have ht := Tits.CompactTits.complex_trace_eq (Tits.CompactTits.square (matrixLineTits x).val)
  rw [Tits.CompactTits.coordinates_square, hX, hSq, Tits.trace3_eq_matrixTrace] at ht
  change firstTitsSquare ((A, 0, 0) : FirstTits ℂ) -
      (Tits.CompactTits.trace (Tits.CompactTits.square (matrixLineTits x).val) / 3) •
        (firstTitsOne : FirstTits ℂ) = (tracelessSquare A, 0, 0)
  rw [hSq]
  apply Prod.ext
  · change A * A -
      (Tits.CompactTits.trace (Tits.CompactTits.square (matrixLineTits x).val) / 3) • (1 : Mat3 ℂ) =
      tracelessSquare A
    change A * A -
      ((↑(Tits.CompactTits.trace (Tits.CompactTits.square (matrixLineTits x).val) / 3) : ℂ) •
        (1 : Mat3 ℂ)) = tracelessSquare A
    rw [Complex.ofReal_div, Complex.ofReal_ofNat, ht]
    rfl
  · simp [firstTitsOne]
    rfl

/-- The matrix-line square is the full ambient equal-strength signed square. -/
theorem matrixLineEmbed_equalSquare (x : TracelessHermitian3) :
    signedEqualCubic.squareMap (matrixLineEmbed x) =
      matrixLineEmbed (matrixEqualCubic.squareMap x) := by
  apply gradedTitsEquiv.injective
  rw [gradedTitsEquiv_signedSquare, gradedTitsEquiv_matrixLineEmbed, gradedTitsEquiv_matrixLineEmbed,
    matrixEqualCubic_squareMap, matrixLineTits_square]

end

end ThirteenPlanes
