module

public import ThirteenPlanes.ClosedBlocks.DerivationCompression
public import ThirteenPlanes.NativeFramesCarrier
public import AlbertDerivationFrame
public import NativeRecoveredCoordinates

@[expose] public section

set_option backward.privateInPublic true

/-! The literal Albert rotation used for compression to a second real block. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open AlbertSequential AlbertSequential.NativeAnalysis

noncomputable section

/-- Recover the native matrix coordinates from the Hilbert trace carrier. -/
def nativeCoordinates : NativeTraceless →ₗ[ℝ] Albert :=
  recoveredCoordinateEquiv.symm.toLinearMap.comp Glennie.traceLinear.ker.subtype

private def rawRotation : AlbertDerivation :=
  (4 : ℝ) • albertInnerDerivation (diagAtom 0) (slotElem01 octOne)

private def fullRotation : Module.End ℝ Glennie.Albert :=
  recoveredCoordinateEquiv.toLinearMap.comp (rawRotation.val.comp recoveredCoordinateEquiv.symm.toLinearMap)

private theorem fullRotation_apply (x : Glennie.Albert) :
    fullRotation x = recoveredCoordinateEquiv (rawRotation.val (recoveredCoordinateEquiv.symm x)) := rfl

private theorem fullRotation_product (x y : Glennie.Albert) :
    fullRotation (Glennie.jordan x y) =
      Glennie.jordan (fullRotation x) y + Glennie.jordan x (fullRotation y) := by
  obtain ⟨a, rfl⟩ := recoveredCoordinateEquiv.surjective x
  obtain ⟨b, rfl⟩ := recoveredCoordinateEquiv.surjective y
  simp only [fullRotation_apply, LinearEquiv.symm_apply_apply]
  rw [← recoveredCoordinateEquiv_jordanMul, LinearEquiv.symm_apply_apply, albertDerivation_mul,
    map_add, recoveredCoordinateEquiv_jordanMul, recoveredCoordinateEquiv_jordanMul]

private theorem fullRotation_unit : fullRotation (1 : Glennie.Albert) = 0 := by
  change recoveredCoordinateEquiv (rawRotation.val (recoveredCoordinateEquiv.symm 1)) = 0
  rw [← recoveredCoordinateEquiv_unit, LinearEquiv.symm_apply_apply, albertDerivation_unit, map_zero]

private theorem fullRotation_formula (x : Glennie.Albert) :
    let a := recoveredCoordinateEquiv (diagAtom 0)
    let b := recoveredCoordinateEquiv (slotElem01 octOne)
    fullRotation x = (4 : ℝ) •
      (Glennie.jordan a (Glennie.jordan b x) - Glennie.jordan b (Glennie.jordan a x)) := by
  dsimp only
  change recoveredCoordinateEquiv ((4 : ℝ) •
    (albertInnerDerivation (diagAtom 0) (slotElem01 octOne)).val (recoveredCoordinateEquiv.symm x)) = _
  rw [albertInnerDerivation_apply, map_smul, map_sub, recoveredCoordinateEquiv_jordanMul,
    recoveredCoordinateEquiv_jordanMul, recoveredCoordinateEquiv_jordanMul,
    recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply]

private theorem fullRotation_skew (x y : Glennie.Albert) :
    Glennie.inner (fullRotation x) y = -Glennie.inner x (fullRotation y) := by
  have selfAdj (a u v : Glennie.Albert) :
      Glennie.inner (Glennie.jordan a u) v = Glennie.inner u (Glennie.jordan a v) := by
    rw [Glennie.jordan_comm a u, Glennie.inner_jordan_associative]
  rw [fullRotation_formula x, fullRotation_formula y]
  simp only [Glennie.inner_smul_left, Glennie.inner_smul_right,
    Glennie.inner_sub_left, Glennie.inner_sub_right, selfAdj]
  ring

private theorem fullRotation_trace_zero (x : Glennie.Albert) : Glennie.trace (fullRotation x) = 0 := by
  rw [← nativeInner_one_right, fullRotation_skew, fullRotation_unit, Glennie.inner_zero_right, neg_zero]

/-- The infinitesimal first-two-coordinate rotation on the actual traceless Albert space. -/
def nativeRotation : Module.End ℝ NativeTraceless :=
  (fullRotation.comp Glennie.traceLinear.ker.subtype).codRestrict _
    (fun x => fullRotation_trace_zero x.val)

theorem nativeRotation_skew (x y : NativeTraceless) :
    ⟪nativeRotation x, y⟫ = -⟪x, nativeRotation y⟫ :=
  fullRotation_skew x.val y.val

private theorem nativeRotation_center (x : Glennie.Albert) :
    nativeRotation (nativeCenter x) = nativeCenter (fullRotation x) := by
  apply Subtype.ext
  change fullRotation (Glennie.traceless x) = Glennie.traceless (fullRotation x)
  rw [Glennie.traceless, Glennie.traceless, map_sub, map_smul, fullRotation_unit,
    fullRotation_trace_zero, zero_div, zero_smul, smul_zero]

theorem nativeRotation_derivation (x y : NativeTraceless) :
    nativeRotation (nativeEqualCubic.L x y) =
      nativeEqualCubic.L (nativeRotation x) y + nativeEqualCubic.L x (nativeRotation y) := by
  have hL (a b : NativeTraceless) : nativeEqualCubic.L a b =
      nativeCenter (Glennie.jordan a.val b.val) := rfl
  have hD (a : NativeTraceless) : (nativeRotation a).val = fullRotation a.val := rfl
  simp only [hL, nativeRotation_center, fullRotation_product, map_add, hD]

private theorem rawSlot01 (x : Albert) :
    (jordanMul (slotElem01 octOne) x).2 0 = ((x.1 0 + x.1 1) / 2) • octOne := by
  rw [jordanMul_off_0]
  change (1 / 2 : ℝ) • ((0 + 0) • x.2 0 + (x.1 0 + x.1 1) • octOne +
    octonionMul 0 (octonionConj (x.2 2)) + octonionMul (x.2 1) (octonionConj 0)) = _
  simp only [add_zero, zero_smul, zero_add, octonionMul_zero_left, octonionConj_zero,
    octonionMul_zero_right, smul_smul]
  rw [mul_comm]
  simp [div_eq_mul_inv]

private theorem rawSlot02 (x : Albert) :
    (jordanMul (slotElem01 octOne) x).2 1 = (1 / 2 : ℝ) • x.2 2 := by
  rw [jordanMul_off_1]
  change (1 / 2 : ℝ) • ((0 + 0) • x.2 1 + (x.1 0 + x.1 2) • (0 : AlbertSequential.Octonion) +
    octonionMul octOne (x.2 2) + octonionMul (x.2 0) 0) = _
  simp [octOne, octonionMul_scalar_left, octonionMul_zero_right]

private theorem rawSlot12 (x : Albert) :
    (jordanMul (slotElem01 octOne) x).2 2 = (1 / 2 : ℝ) • x.2 1 := by
  rw [jordanMul_off_2]
  change (1 / 2 : ℝ) • ((0 + 0) • x.2 2 + (x.1 1 + x.1 2) • (0 : AlbertSequential.Octonion) +
    octonionMul (octonionConj octOne) (x.2 1) + octonionMul (octonionConj (x.2 0)) 0) = _
  simp [octOne, octonionConj_scalar, octonionMul_scalar_left, octonionMul_zero_right]

/-- On the zero-diagonal space the rotation fixes the first slot at zero speed
and exchanges the two remaining upper slots with opposing unit speeds. -/
theorem nativeRotation_upper_slots (x : NativeTraceless)
    (hd : ∀ i, (nativeCoordinates x).1 i = 0) :
    (nativeCoordinates (nativeRotation x)).2 0 = 0 ∧
    (nativeCoordinates (nativeRotation x)).2 1 = (nativeCoordinates x).2 2 ∧
    (nativeCoordinates (nativeRotation x)).2 2 = -(nativeCoordinates x).2 1 := by
  let X := nativeCoordinates x
  have hX : nativeCoordinates (nativeRotation x) = rawRotation.val X := by
    change recoveredCoordinateEquiv.symm (recoveredCoordinateEquiv (rawRotation.val X)) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [hX]
  have action (i : Fin 3) :
      (rawRotation.val X).2 i = (4 : ℝ) •
        ((jordanMul (diagAtom 0) (jordanMul (slotElem01 octOne) X)).2 i -
         (jordanMul (slotElem01 octOne) (jordanMul (diagAtom 0) X)).2 i) := by
    change ((4 : ℝ) • (albertInnerDerivation (diagAtom 0) (slotElem01 octOne)).val X).2 i = _
    rw [albertInnerDerivation_apply]
    rfl
  have w0 : derivationSlotWeight 0 0 = 1 / 2 := by norm_num [derivationSlotWeight, derivationFirst, derivationSecond]
  have w1 : derivationSlotWeight 0 1 = 1 / 2 := by norm_num [derivationSlotWeight, derivationFirst, derivationSecond]
  have w2 : derivationSlotWeight 0 2 = 0 := by norm_num [derivationSlotWeight, derivationFirst, derivationSecond]
  refine ⟨?_, ?_, ?_⟩
  · rw [action, jordanMul_diagAtom_offDiagonal, rawSlot01, rawSlot01,
      jordanMul_diagAtom_diagonal, jordanMul_diagAtom_diagonal, w0]
    simp [hd, X]
  · rw [action, jordanMul_diagAtom_offDiagonal, rawSlot02, rawSlot02,
      jordanMul_diagAtom_offDiagonal, w1, w2]
    simp only [zero_smul, smul_zero, sub_zero, smul_smul]
    norm_num [X]
  · rw [action, jordanMul_diagAtom_offDiagonal, rawSlot12, rawSlot12,
      jordanMul_diagAtom_offDiagonal, w1, w2]
    simp only [smul_smul, zero_mul, zero_smul, zero_sub, smul_neg, ← mul_assoc,
      show (4 : ℝ) * (1 / 2) * (1 / 2) = 1 by norm_num, one_smul, X]

end

end ThirteenPlanes.ClosedBlocks
