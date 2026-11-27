module

public import ThirteenPlanes.Peirce.SlotPolynomialTransport
public import ThirteenPlanes.Peirce.SlotQuaternionModel
public import ThirteenPlanes.OrthogonalIsotope

@[expose] public section

set_option backward.privateInPublic true

/-! Marked identification with the actual quaternion trace cubic. -/

open scoped Quaternion InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

private def quaternionConjLIE : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ where
  toLinearEquiv :=
    { toFun := star
      invFun := star
      left_inv := star_star
      right_inv := star_star
      map_add' := star_add
      map_smul' := fun c x => by simp only [star_smul, star_trivial, RingHom.id_apply] }
  norm_map' := Quaternion.norm_star

private theorem hurwitz_quaternion {S₁ S₂ S₃ : Type*}
    [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁] [FiniteDimensional ℝ S₁]
    [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂] [FiniteDimensional ℝ S₂]
    [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃] [FiniteDimensional ℝ S₃]
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (hφ : ∀ u p, ‖φ u p‖ = ‖u‖ * ‖p‖)
    (h₁ : Module.finrank ℝ S₁ = 4) (h₂ : Module.finrank ℝ S₂ = 4) (h₃ : Module.finrank ℝ S₃ = 4) :
    Nonempty (MarkedPlane.HurwitzIsotopy φ (fun x y : Quaternion ℝ => x * y)) := by
  rcases (MarkedPlane.orthogonalProduct_isotopicToHurwitz φ hφ
    (by decide : 0 < 4) h₁ h₂ h₃).2 with h | h | h | h
  · omega
  · omega
  · exact h.2
  · omega

set_option maxHeartbeats 1200000 in
/-- The marked quaternionic identification of a round cubic with trace-free multiplication at the
idempotent and three four-dimensional slots. The result is an onto trace isometry. -/
theorem markedRoundCubic_quaternion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {h : SymmetricCubic V} {a : V} {b : minusSpace h a}
    (round : IsRound h 1) (ha : IsUnitIdempotent h a) (hb : ‖b‖ = 1)
    (ht : LinearMap.trace ℝ V (h.L a) = 0) (hV : Module.finrank ℝ V = 14) :
    ∃ I : V ≃ₗᵢ[ℝ] QuaternionicMUB.TracelessHilbert,
      I a = quaternionCartanField 1 0 0 0 0 ∧ I b = quaternionCartanField 0 1 0 0 0 ∧
      h = quaternionCartanCubic.pullback I.toLinearMap := by
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
  obtain ⟨R⟩ := hurwitz_quaternion
    (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
    φ hφ h₁ h₂ h₃
  exact slotCubic_isometry_of_model_coordinates
      (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
      (roundSlotCoordinates round ha hb) h
      quaternionCartanCubic φ (roundSlot_normalConditions round ha hb) quaternionCartanEquiv
      (fun p q : Quaternion ℝ => q * star p) quaternionCartanField_norm_sq quaternionCartanCubic_normalForm
      R.left (R.right.trans quaternionConjLIE) (R.output.trans quaternionConjLIE) (by
        intro u p
        change star (R.output (φ u p)) = star (R.right p) * star (R.left u)
        exact (congrArg star (R.map_mul u p)).trans (star_mul _ _))

end

end ThirteenPlanes.Peirce
