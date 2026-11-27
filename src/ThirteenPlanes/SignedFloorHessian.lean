module

public import ThirteenPlanes.SignedSkewStabilizer
public import ThirteenPlanes.Thirteen

@[expose] public section

set_option backward.privateInPublic true

/-! The actual normalized 26-field minimum and its numerical Hessian spectrum. -/

namespace ThirteenPlanes

noncomputable section

/-- The positive equal-strength tensor in the normalized one-loop coupling. -/
def signedFloorCubic : SymmetricCubic SignedField := Real.sqrt (1/3) • signedEqualCubic

private theorem signedFloor_strength_sq : (Real.sqrt (1/3)) ^ 2 = 1/3 :=
  Real.sq_sqrt (by norm_num)

/-- The normalized signed floor point has the exact scalar double-contraction mass. -/
theorem signedFloorCubic_mass : signedFloorCubic.doubleContraction = (7/9 : ℝ) • LinearMap.id := by
  let r := Real.sqrt (1/3)
  have h := signed_contractionLaws.double (r,r)
  rw [coupling_same, signedPair_at_one] at h
  change signedFloorCubic.doubleContraction = _ at h
  rw [h]
  change (r ^ 2 / 3 + 2*r ^ 2) • (LinearMap.id : SignedField →ₗ[ℝ] SignedField) = _
  rw [show r^2 = 1/3 from signedFloor_strength_sq]
  norm_num

/-- The normalized signed floor point has the exact triangle coefficient. -/
theorem signedFloorCubic_triangle : signedFloorCubic.triangleContraction = (-1/3 : ℝ) • signedFloorCubic := by
  let r := Real.sqrt (1/3)
  have h := signed_contractionLaws.triangle (r,r)
  rw [coupling_same, signedPair_at_one] at h
  change signedFloorCubic.triangleContraction = _ at h
  rw [h]
  have hP : familyP 2 (r,r) = -(r^3) := by unfold familyP; simp; ring
  have hQ : familyQ 2 (r,r) = -(r^3) := by unfold familyQ; simp; ring
  rw [hP, hQ, coupling_same, signedPair_at_one]
  change (-(r^3)) • signedEqualCubic = (-1/3 : ℝ) • (r • signedEqualCubic)
  rw [smul_smul]
  congr 1
  rw [pow_succ, show r^2 = 1/3 from signedFloor_strength_sq]
  ring

/-- The normalized signed floor point is fixed by the actual physical-time beta. -/
theorem signedFloorCubic_fixed : oneLoopBeta (16 * Real.pi ^ 2)⁻¹ signedFloorCubic = 0 := by
  have hpi : (16 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hlin : (8 * Real.pi ^ 2 * (16 * Real.pi ^ 2)⁻¹ : ℝ) = 1/2 := by
    field_simp
    ring
  rw [oneLoopBeta, signedFloorCubic_mass, signedFloorCubic_triangle,
    SymmetricCubic.insert_smul_id, hlin, smul_smul, smul_smul]
  module

/-- The actual potential takes its floor value at the normalized signed tensor. -/
theorem signedFloorCubic_aFunction : aFunction signedFloorCubic = floorValue (Module.finrank ℝ SignedField) := by
  have ht := LinearMap.trace_id (R := ℝ) (M := SignedField)
  rw [signedField_finrank] at ht
  have hpair : signedFloorCubic.tensorPairing signedFloorCubic = 182/9 := by
    rw [SymmetricCubic.tensorPairing_self, signedFloorCubic_mass, map_smul, ht]
    norm_num
  have hid : (LinearMap.id : SignedField →ₗ[ℝ] SignedField) * LinearMap.id = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rfl
  have hmass : signedFloorCubic.doubleTraceSq = 1274/81 := by
    rw [SymmetricCubic.doubleTraceSq, signedFloorCubic_mass, smul_mul_assoc, mul_smul_comm,
      hid, smul_smul, map_smul, ht]
    norm_num
  rw [aFunction, SymmetricCubic.tetrahedron, signedFloorCubic_triangle,
    SymmetricCubic.tensorPairing_smul_right, hpair, hmass, signedField_finrank]
  norm_num [floorValue, floorStrength]

/-- The actual signed 26-field minimum has numerical Hessian multiplicities 273, 26 and 2977. -/
theorem signedFloorCubic_hessian_multiplicities :
    Module.finrank ℝ (SymmetricCubic SignedField) = 3276 ∧ Module.finrank ℝ (skewEnd SignedField) = 325 ∧
    Module.finrank ℝ (rotationSpace signedFloorCubic) = 273 ∧ Module.finrank ℝ (traceSpace SignedField) = 26 ∧
    Module.finrank ℝ (complementSpace signedFloorCubic) = 2977 ∧
    traceEigenvalue (Module.finrank ℝ SignedField) = 23 / 9 := by
  have hr : Real.sqrt (1/3) ≠ 0 := by positivity
  exact hessian_multiplicities_twentySix signedField_finrank signedFloorCubic_aFunction
    (signedSkewStabilizer_smul_finrank hr)

end

end ThirteenPlanes
