module

public import ThirteenPlanes.Cubic
public import ThirteenPlanes.SignedPlanes

@[expose] public section

set_option backward.privateInPublic true

/-! Exact triangle cancellation for exterior cubic tensors. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes
namespace ChargeFixed

noncomputable section

/-- A real cubic which transfers an orthogonal complex structure between its slots has
zero triangle contraction. Conjugating a product of three slices by the complex
structure reverses its sign. -/
theorem triangle_zero_of_complex_rotation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (h : SymmetricCubic V) (J : V ≃ₗᵢ[ℝ] V)
    (hJ : ∀ x, J (J x) = -x)
    (hhol : ∀ x y z, h.apply (J x) y z = h.apply x (J y) z) : h.triangleContraction = 0 := by
  let j := J.toLinearEquiv.toLinearMap
  let k := J.symm.toLinearEquiv.toLinearMap
  have hskew (x y : V) : ⟪J x,y⟫ = -⟪x,J y⟫ := by
    calc
      _ = ⟪J x,-J (J y)⟫ := by rw [hJ, neg_neg]
      _ = _ := by rw [inner_neg_right, J.inner_map_map]
  have hanti (x : V) : h.L x * j = -(j * h.L x) := by
    ext y
    apply ext_inner_right ℝ
    intro z
    change h.apply x (J y) z = ⟪-J (h.L x y),z⟫
    rw [inner_neg_left, hskew, neg_neg]
    change h.apply x (J y) z = h.apply x y (J z)
    rw [h.apply_swap₁₂ x (J y) z, h.apply_swap₂₃ (J y) x z,
      hhol y z x, h.apply_swap₂₃ y (J z) x, h.apply_swap₁₂ y x (J z)]
  have hjk : j*k = 1 := by ext x; exact J.apply_symm_apply x
  have hkj : k*j = 1 := by ext x; exact J.symm_apply_apply x
  apply SymmetricCubic.ext
  intro x y z
  rw [SymmetricCubic.apply_triangleContraction]
  let A := h.L x
  let B := h.L y
  let C := h.L z
  let P := A*B*C
  have hr : P*j = -(j*P) := by
    unfold P
    calc
      (A*B*C)*j = A*(B*(C*j)) := by noncomm_ring
      _ = -(A*(B*j)*C) := by rw [hanti z]; noncomm_ring
      _ = A*j*B*C := by rw [hanti y]; noncomm_ring
      _ = -(j*(A*B*C)) := by rw [hanti x]; noncomm_ring
  have hz : LinearMap.trace ℝ V P = -LinearMap.trace ℝ V P := by
    calc
      _ = LinearMap.trace ℝ V (P*j*k) := by rw [mul_assoc, hjk, mul_one]
      _ = -LinearMap.trace ℝ V (j*P*k) := by rw [hr, neg_mul, map_neg]
      _ = _ := by rw [LinearMap.trace_mul_cycle ℝ j P k, hkj, one_mul]
  rw [SymmetricCubic.apply_zero]
  change LinearMap.trace ℝ V P = 0
  linarith

/-- Multiplication by `i` in a charge representative with third coordinate one. The
opposite representative uses `-i`, and the zero-third-coordinate planes use `i`. -/
def exteriorRotationFactor (p : SignedPlaneIndex) : ℂ :=
  if p.val.val 2 = -1 then -Complex.I else Complex.I

private theorem exteriorRotationFactor_square (p : SignedPlaneIndex) :
    exteriorRotationFactor p * exteriorRotationFactor p = -1 := by
  unfold exteriorRotationFactor
  split_ifs <;> simp [← pow_two, Complex.I_sq]

private theorem exteriorRotationFactor_norm (p : SignedPlaneIndex) : ‖exteriorRotationFactor p‖ = 1 := by
  unfold exteriorRotationFactor
  split_ifs <;> simp

private def planeQuarterTurn : (SignedPlaneIndex → ℂ) ≃ₗ[ℝ] (SignedPlaneIndex → ℂ) where
  toFun x p := exteriorRotationFactor p * x p
  invFun x p := -exteriorRotationFactor p * x p
  left_inv x := by
    funext p
    have h := exteriorRotationFactor_square p
    change -exteriorRotationFactor p * (exteriorRotationFactor p * x p) = x p
    linear_combination -x p * h
  right_inv x := by
    funext p
    have h := exteriorRotationFactor_square p
    change exteriorRotationFactor p * (-exteriorRotationFactor p * x p) = x p
    linear_combination -x p * h
  map_add' x y := by funext p; exact mul_add _ _ _
  map_smul' r x := by funext p; change _ * ((r : ℂ) * _) = (r : ℂ) * (_ * _); ring

private def signedQuarterTurnEquiv : SignedField ≃ₗ[ℝ] SignedField :=
  signedPlaneCoordinates.trans (planeQuarterTurn.trans signedPlaneCoordinates.symm)

@[simp] theorem quarterTurn_coordinates (x : SignedField) (p : SignedPlaneIndex) :
    signedPlaneCoordinates (signedQuarterTurnEquiv x) p =
      exteriorRotationFactor p * signedPlaneCoordinates x p := by
  change signedPlaneCoordinates (signedPlaneCoordinates.symm (planeQuarterTurn
    (signedPlaneCoordinates x))) p = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- An orthogonal complex structure on the signed fields, oriented by the affine exterior grades. -/
def signedExteriorRotation : SignedField ≃ₗᵢ[ℝ] SignedField where
  toLinearEquiv := signedQuarterTurnEquiv
  norm_map' x := by
    change ‖signedQuarterTurnEquiv x‖ = ‖x‖
    have h : ‖signedQuarterTurnEquiv x‖^2 = ‖x‖^2 := by
      simp_rw [signedField_norm_sq_representatives, quarterTurn_coordinates, norm_mul,
        exteriorRotationFactor_norm, one_mul]
    nlinarith [norm_nonneg (signedQuarterTurnEquiv x), norm_nonneg x]

@[simp] theorem signedExteriorRotation_sq (x : SignedField) :
    signedExteriorRotation (signedExteriorRotation x) = -x := by
  apply signedPlaneCoordinates.injective
  funext p
  change signedPlaneCoordinates (signedQuarterTurnEquiv (signedQuarterTurnEquiv x)) p = _
  rw [quarterTurn_coordinates, quarterTurn_coordinates, ← mul_assoc, exteriorRotationFactor_square]
  simp

theorem signedExteriorRotation_at_third_one (x : SignedField) (u : NonzeroCharge)
    (hu : u.val 2 = 1) :
    signedCoordinates (signedExteriorRotation x) u = Complex.I * signedCoordinates x u := by
  by_cases hrep : isChargeRepresentative u.val
  · let p : SignedPlaneIndex := ⟨u,hrep⟩
    change signedPlaneCoordinates (signedQuarterTurnEquiv x) p = Complex.I * signedPlaneCoordinates x p
    rw [quarterTurn_coordinates]
    have hp : p.val.val 2 ≠ -1 := by
      change u.val 2 ≠ -1
      rw [hu]
      decide
    rw [exteriorRotationFactor, ite_eq_right hp]
  · let p : SignedPlaneIndex := ⟨oppositeCharge u,(oppositeCharge_isRepresentative_iff u).mpr hrep⟩
    have hj : signedCoordinates (signedExteriorRotation x) (oppositeCharge u) =
        -Complex.I * signedCoordinates x (oppositeCharge u) := by
      change signedPlaneCoordinates (signedQuarterTurnEquiv x) p = -Complex.I * signedPlaneCoordinates x p
      rw [quarterTurn_coordinates]
      have hp : p.val.val 2 = -1 := by change -(u.val 2) = -1; rw [hu]
      rw [exteriorRotationFactor, ite_eq_left hp]
    rw [signedCoordinates_opposite, signedCoordinates_opposite] at hj
    simpa [Complex.star_def] using congrArg star hj

theorem signedExteriorRotation_at_third_neg_one (x : SignedField) (u : NonzeroCharge)
    (hu : u.val 2 = -1) :
    signedCoordinates (signedExteriorRotation x) u = -Complex.I * signedCoordinates x u := by
  have h := signedExteriorRotation_at_third_one x (oppositeCharge u) (by
    change -(u.val 2) = 1
    rw [hu, neg_neg])
  rw [signedCoordinates_opposite, signedCoordinates_opposite] at h
  simpa [Complex.star_def] using congrArg star h

/-- Any actual signed cubic with its grade expansion supported on equal nonzero third
coordinates has no triangle term. -/
theorem triangle_zero_of_exterior_expansion (h : SymmetricCubic SignedField)
    (a : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (support : ∀ i j k, a i j k ≠ 0 → i.val 2 = j.val 2 ∧ j.val 2 = k.val 2 ∧ i.val 2 ≠ 0)
    (expansion : ∀ x y z, h.apply x y z = ∑ i, ∑ j, ∑ k,
      (a i j k * signedCoordinates x i * signedCoordinates y j * signedCoordinates z k).re) :
    h.triangleContraction = 0 := by
  apply triangle_zero_of_complex_rotation h signedExteriorRotation signedExteriorRotation_sq
  intro x y z
  rw [expansion, expansion]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => ?_)))
  by_cases hz : a i j k = 0
  · simp [hz]
  · obtain ⟨he,_,hi⟩ := support i j k hz
    have hr : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
    apply congrArg Complex.re
    rcases hr _ hi with hp|hp
    · rw [signedExteriorRotation_at_third_one x i hp,
        signedExteriorRotation_at_third_one y j (he.symm.trans hp)]
      ring
    · rw [signedExteriorRotation_at_third_neg_one x i hp,
        signedExteriorRotation_at_third_neg_one y j (he.symm.trans hp)]
      ring

end
end ChargeFixed
end ThirteenPlanes
