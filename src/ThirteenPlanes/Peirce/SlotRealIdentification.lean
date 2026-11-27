module

public import ThirteenPlanes.Peirce.SlotPolynomialTransport
public import ThirteenPlanes.Peirce.SlotRealModel
public import ThirteenPlanes.OrthogonalIsotope

@[expose] public section

set_option backward.privateInPublic true

/-! Marked identification with the actual real trace cubic. -/

open scoped Quaternion InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

private theorem hurwitz_real {S₁ S₂ S₃ : Type*}
    [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁] [FiniteDimensional ℝ S₁]
    [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂] [FiniteDimensional ℝ S₂]
    [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃] [FiniteDimensional ℝ S₃]
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (hφ : ∀ u p, ‖φ u p‖ = ‖u‖ * ‖p‖)
    (h₁ : Module.finrank ℝ S₁ = 1) (h₂ : Module.finrank ℝ S₂ = 1) (h₃ : Module.finrank ℝ S₃ = 1) :
    Nonempty (MarkedPlane.HurwitzIsotopy φ (fun x y : ℝ => x * y)) := by
  rcases (MarkedPlane.orthogonalProduct_isotopicToHurwitz φ hφ
    (by decide : 0 < 1) h₁ h₂ h₃).2 with h | h | h | h
  · exact h.2
  · omega
  · omega
  · omega

set_option maxHeartbeats 1200000 in
/-- The marked real identification of a round cubic with trace-free multiplication at the
idempotent and three one-dimensional slots. The result is an onto trace isometry. -/
theorem markedRoundCubic_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {h : SymmetricCubic V} {a : V} {b : minusSpace h a}
    (round : IsRound h 1) (ha : IsUnitIdempotent h a) (hb : ‖b‖ = 1)
    (ht : LinearMap.trace ℝ V (h.L a) = 0) (hV : Module.finrank ℝ V = 5) :
    ∃ I : V ≃ₗᵢ[ℝ] RealTracelessSymmetric3,
      I a = realCartanEquiv (1, 0, 0, 0, 0) ∧ I b = realCartanEquiv (0, 1, 0, 0, 0) ∧
      h = realCartanCubic.pullback I.toLinearMap := by
  have hk : 0 < (Module.finrank ℝ V - 2) / 3 := by norm_num [hV]
  obtain ⟨h₁, h₂, h₃⟩ := slot_finranks round ha hb ht hk
  norm_num [hV] at h₁ h₂ h₃
  let φ : ↥(slotOne b) →ₗ[ℝ] ↥(slotTwo round ha b) →ₗ[ℝ] ↥(slotThree round ha b) :=
    slotProduct round ha (b := b)
  let : FiniteDimensional ℝ ↥(slotOne b) :=
    FiniteDimensional.of_injective (slotOne b).subtype (slotOne b).subtype_injective
  let : FiniteDimensional ℝ ↥(halfSpace h a) :=
    FiniteDimensional.of_injective (halfSpace h a).subtype (halfSpace h a).subtype_injective
  let : FiniteDimensional ℝ ↥(slotTwo round ha b) :=
    FiniteDimensional.of_injective (slotTwo round ha b).subtype (slotTwo round ha b).subtype_injective
  let : FiniteDimensional ℝ ↥(slotThree round ha b) :=
    FiniteDimensional.of_injective (slotThree round ha b).subtype (slotThree round ha b).subtype_injective
  let : InnerProductSpace ℝ ↥(minusSpace h a) := Submodule.innerProductSpace _
  let : InnerProductSpace ℝ ↥(halfSpace h a) := Submodule.innerProductSpace _
  let : InnerProductSpace ℝ ↥(slotOne b) := Submodule.innerProductSpace _
  let : InnerProductSpace ℝ ↥(slotTwo round ha b) := Submodule.innerProductSpace _
  let : InnerProductSpace ℝ ↥(slotThree round ha b) := Submodule.innerProductSpace _
  have hφ (u : ↥(slotOne b)) (p : ↥(slotTwo round ha b)) : ‖φ u p‖ = ‖u‖ * ‖p‖ :=
    slotProduct_norm round ha u p
  obtain ⟨R⟩ := hurwitz_real
    (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
    φ hφ h₁ h₂ h₃
  exact slotCubic_isometry_of_model_coordinates
      (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
      (roundSlotCoordinates round ha hb) h
      realCartanCubic φ (roundSlot_normalConditions round ha hb) realCartanEquiv
      (fun p q : ℝ => q * p) realCartanField_norm_sq realCartanCubic_normalForm
      R.left R.right R.output (fun u p => (R.map_mul u p).trans (mul_comm _ _))

end

end ThirteenPlanes.Peirce
