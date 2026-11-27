module

public import ThirteenPlanes.Peirce.SlotPolynomialTransport
public import ThirteenPlanes.Peirce.SlotComplexModel
public import ThirteenPlanes.Peirce.SlotNativeModel
public import ThirteenPlanes.Peirce.PlaneCounts

@[expose] public section

set_option backward.privateInPublic true

/-! Marked identifications with the actual complex Hermitian and native Albert cubics. -/

open scoped Quaternion InnerProductSpace RealInnerProductSpace ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean

namespace ThirteenPlanes.Peirce

noncomputable section

local notation "𝕆ₙ" => AlbertSequential.Octonion

private theorem nativeOctonion_norm_sq_glennie (x : 𝕆ₙ) : ‖x‖ ^ 2 = Glennie.octNormSq x := by
  rw [← real_inner_self_eq_norm_sq, MarkedPlane.nativeOctonion_inner]
  exact Glennie.octDot_self x

private theorem hurwitz_complex {S₁ S₂ S₃ : Type*}
    [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁] [FiniteDimensional ℝ S₁]
    [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂] [FiniteDimensional ℝ S₂]
    [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃] [FiniteDimensional ℝ S₃]
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (hφ : ∀ u p, ‖φ u p‖ = ‖u‖ * ‖p‖)
    (h₁ : Module.finrank ℝ S₁ = 2) (h₂ : Module.finrank ℝ S₂ = 2) (h₃ : Module.finrank ℝ S₃ = 2) :
    Nonempty (MarkedPlane.HurwitzIsotopy φ (fun x y : ℂ => x * y)) := by
  rcases (MarkedPlane.orthogonalProduct_isotopicToHurwitz φ hφ
    (by decide : 0 < 2) h₁ h₂ h₃).2 with h | h | h | h
  · omega
  · exact h.2
  · omega
  · omega

set_option maxHeartbeats 1200000 in
/-- The marked complex identification of a round cubic with trace-free multiplication at the
idempotent and three two-dimensional slots. The result is an onto trace isometry. -/
theorem markedRoundCubic_complex {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {h : SymmetricCubic V} {a : V} {b : minusSpace h a}
    (round : IsRound h 1) (ha : IsUnitIdempotent h a) (hb : ‖b‖ = 1)
    (ht : LinearMap.trace ℝ V (h.L a) = 0) (hV : Module.finrank ℝ V = 8) :
    ∃ I : V ≃ₗᵢ[ℝ] TracelessHermitian3,
      I a = complexCartanField 1 0 0 0 0 ∧ I b = complexCartanField 0 1 0 0 0 ∧
      h = complexCartanCubic.pullback I.toLinearMap := by
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
  obtain ⟨R⟩ := hurwitz_complex
    (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
    φ hφ h₁ h₂ h₃
  exact slotCubic_isometry_of_model_coordinates
      (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
      (roundSlotCoordinates round ha hb) h
      complexCartanCubic φ (roundSlot_normalConditions round ha hb) complexCartanEquiv
      (fun p q : ℂ => q * star p) complexCartanField_norm_sq complexCartanCubic_normalForm
      R.left (R.right.trans Complex.conjLIE) (R.output.trans Complex.conjLIE) (by
        intro u p
        change star (R.output (φ u p)) = star (R.right p) * star (R.left u)
        exact (congrArg star (R.map_mul u p)).trans (star_mul _ _))
private def nativeCartanConj : 𝕆ₙ ≃ₗᵢ[ℝ] 𝕆ₙ where
  toLinearEquiv :=
    { toFun := AlbertSequential.octonionConj
      invFun := AlbertSequential.octonionConj
      left_inv := fun x => Glennie.octConj_conj x
      right_inv := fun x => Glennie.octConj_conj x
      map_add' := fun x y => Glennie.octConj_add x y
      map_smul' := fun c x => Glennie.octConj_smul c x }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖AlbertSequential.octonionConj x‖ ^ 2 = ‖x‖ ^ 2
    rw [nativeOctonion_norm_sq_glennie, nativeOctonion_norm_sq_glennie]
    exact Glennie.octNormSq_conj x

private theorem hurwitz_native {S₁ S₂ S₃ : Type*}
    [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁] [FiniteDimensional ℝ S₁]
    [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂] [FiniteDimensional ℝ S₂]
    [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃] [FiniteDimensional ℝ S₃]
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (hφ : ∀ u p, ‖φ u p‖ = ‖u‖ * ‖p‖)
    (h₁ : Module.finrank ℝ S₁ = 8) (h₂ : Module.finrank ℝ S₂ = 8) (h₃ : Module.finrank ℝ S₃ = 8) :
    Nonempty (MarkedPlane.HurwitzIsotopy φ AlbertSequential.octonionMul) := by
  rcases (MarkedPlane.orthogonalProduct_isotopicToHurwitz φ hφ
    (by decide : 0 < 8) h₁ h₂ h₃).2 with h | h | h | h
  · omega
  · omega
  · omega
  · exact h.2

set_option maxHeartbeats 1200000 in
/-- The marked octonionic identification is an onto isometry to the actual trace-free
native Albert space, intertwining the whole normalized Jordan trace cubic. -/
theorem markedRoundCubic_native {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {h : SymmetricCubic V} {a : V} {b : minusSpace h a}
    (round : IsRound h 1) (ha : IsUnitIdempotent h a) (hb : ‖b‖ = 1)
    (ht : LinearMap.trace ℝ V (h.L a) = 0) (hV : Module.finrank ℝ V = 26) :
    ∃ I : V ≃ₗᵢ[ℝ] NativeTraceless,
      I a = nativeCartanField 1 0 0 0 0 ∧ I b = nativeCartanField 0 1 0 0 0 ∧
      h = nativeCartanCubic.pullback I.toLinearMap := by
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
  obtain ⟨R⟩ := hurwitz_native
    (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
    φ hφ h₁ h₂ h₃
  exact slotCubic_isometry_of_model_coordinates
      (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
      (roundSlotCoordinates round ha hb) h
      nativeCartanCubic φ (roundSlot_normalConditions round ha hb) nativeCartanEquiv
      (fun p q => AlbertSequential.octonionMul q (AlbertSequential.octonionConj p))
      nativeCartanField_norm_sq nativeCartanCubic_normalForm
      R.left (R.right.trans nativeCartanConj) (R.output.trans nativeCartanConj) (by
        intro u p
        change AlbertSequential.octonionConj (R.output (φ u p)) = AlbertSequential.octonionMul
          (AlbertSequential.octonionConj (R.right p)) (AlbertSequential.octonionConj (R.left u))
        exact (congrArg AlbertSequential.octonionConj (R.map_mul u p)).trans
          (Glennie.octConj_mul (R.left u) (R.right p)))
end

end ThirteenPlanes.Peirce
