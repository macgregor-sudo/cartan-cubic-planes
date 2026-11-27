module

public import ThirteenPlanes.Peirce.SlotClosedPlaneIdentification
public import ThirteenPlanes.Peirce.SlotRealIdentification
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

/-! The marked Cartan identifications for harmonic round cubics and for proper plane systems. -/

open scoped InnerProductSpace RealInnerProductSpace ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean

namespace ThirteenPlanes.Peirce

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {h : SymmetricCubic V} {a : V}

/-- A positive common dimension of three genuine marked slots is a Hurwitz dimension. -/
theorem markedSlot_dimension_cases (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    (b : minusSpace h a) (hb : ‖b‖ = 1) (ht : LinearMap.trace ℝ V (h.L a) = 0)
    (hk : 0 < (Module.finrank ℝ V - 2) / 3) :
    let k := (Module.finrank ℝ V - 2) / 3
    k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 := by
  obtain ⟨h₁, h₂, h₃⟩ := slot_finranks round ha hb ht hk
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
  let φ : ↥(slotOne b) →ₗ[ℝ] ↥(slotTwo round ha b) →ₗ[ℝ] ↥(slotThree round ha b) :=
    slotProduct round ha (b := b)
  have hφ (u : ↥(slotOne b)) (p : ↥(slotTwo round ha b)) : ‖φ u p‖ = ‖u‖ * ‖p‖ :=
    slotProduct_norm round ha u p
  exact (MarkedPlane.orthogonalProduct_isotopicToHurwitz
    (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo round ha b)) (S₃ := ↥(slotThree round ha b))
    φ hφ hk h₁ h₂ h₃).1

/-- Theorem 2b-general(ii). The ambient dimension selects the actual trace carrier,
and every unit minus mark yields an onto trace isometry with the two prescribed diagonal marks. -/
/- This identifies the marked harmonic eikonal cubic with one of Élie Cartan's cubic models
using the Peirce slots and Hurwitz's classification. See Cartan (1939), Part I, §I,
doi:10.1007/BF01580289. -/
theorem harmonicRoundCubic_identification (round : IsRound h 1) (harmonic : h.TraceFree)
    (ha : IsUnitIdempotent h a) (hn : 3 ≤ Module.finrank ℝ V) :
    let k := (Module.finrank ℝ V - 2) / 3
    minusSpace h a ≠ ⊥ ∧ Module.finrank ℝ V = 3 * k + 2 ∧
      (k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8) ∧
      ∀ (b : minusSpace h a), ‖b‖ = 1 →
        (k = 1 ∧ ∃ I : V ≃ₗᵢ[ℝ] RealTracelessSymmetric3,
          I a = realCartanEquiv (1, 0, 0, 0, 0) ∧ I b = realCartanEquiv (0, 1, 0, 0, 0) ∧
          h = realCartanCubic.pullback I.toLinearMap) ∨
        (k = 2 ∧ ∃ I : V ≃ₗᵢ[ℝ] TracelessHermitian3,
          I a = complexCartanField 1 0 0 0 0 ∧ I b = complexCartanField 0 1 0 0 0 ∧
          h = complexCartanCubic.pullback I.toLinearMap) ∨
        (k = 4 ∧ ∃ I : V ≃ₗᵢ[ℝ] QuaternionicMUB.TracelessHilbert,
          I a = quaternionCartanField 1 0 0 0 0 ∧ I b = quaternionCartanField 0 1 0 0 0 ∧
          h = quaternionCartanCubic.pullback I.toLinearMap) ∨
        (k = 8 ∧ ∃ I : V ≃ₗᵢ[ℝ] NativeTraceless,
          I a = nativeCartanField 1 0 0 0 0 ∧ I b = nativeCartanField 0 1 0 0 0 ∧
          h = nativeCartanCubic.pullback I.toLinearMap) := by
  dsimp only
  have ht := harmonic a
  obtain ⟨_, hminus_dim, _⟩ := finrank_exact_of_trace_zero round ha ht
  have hpos : 0 < Module.finrank ℝ (minusSpace h a) := by omega
  have hk : 0 < (Module.finrank ℝ V - 2) / 3 := by omega
  have hn' : Module.finrank ℝ V = 3 * ((Module.finrank ℝ V - 2) / 3) + 2 := by omega
  have hminus_ne : minusSpace h a ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hpos
    omega
  let : Nontrivial ↥(minusSpace h a) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨b₀, hb₀⟩ := exists_norm_eq ↥(minusSpace h a) (by norm_num : (0 : ℝ) ≤ 1)
  have hcases := markedSlot_dimension_cases round ha b₀ hb₀ ht hk
  refine ⟨hminus_ne, hn', hcases, fun b hb => ?_⟩
  rcases hcases with hcase | hcase | hcase | hcase
  · exact Or.inl ⟨hcase, markedRoundCubic_real round ha hb ht (by omega)⟩
  · exact Or.inr (Or.inl ⟨hcase, markedRoundCubic_complex round ha hb ht (by omega)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hcase, markedRoundCubic_quaternion round ha hb ht (by omega)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hcase, markedRoundCubic_native round ha hb ht (by omega)⟩))

/-- Theorem 2b-ident. The proper closed-plane count selects an actual normalized
Cartan model, identifies the entire cubic, and carries the selected plane onto the diagonals. -/
theorem closedPlaneSystem_identification {ι : Type*} [Fintype ι] {planes : PlaneDecomposition V ι}
    (round : IsRound h 1) (closed : IsClosedPlaneSystem h planes) (proper : 1 < Fintype.card ι) (i : ι) :
    let k := 2 * (Fintype.card ι - 1) / 3
    (k = 2 ∧ Fintype.card ι = 4 ∧ ∃ I : V ≃ₗᵢ[ℝ] TracelessHermitian3,
      h = complexCartanCubic.pullback I.toLinearMap ∧ ∀ w,
        w ∈ (planes.plane i).map I.toLinearMap ↔ ∃ α β : ℝ, w = complexCartanField α β 0 0 0) ∨
    (k = 4 ∧ Fintype.card ι = 7 ∧ ∃ I : V ≃ₗᵢ[ℝ] QuaternionicMUB.TracelessHilbert,
      h = quaternionCartanCubic.pullback I.toLinearMap ∧ ∀ w,
        w ∈ (planes.plane i).map I.toLinearMap ↔ ∃ α β : ℝ, w = quaternionCartanField α β 0 0 0) ∨
    (k = 8 ∧ Fintype.card ι = 13 ∧ ∃ I : V ≃ₗᵢ[ℝ] NativeTraceless,
      h = nativeCartanCubic.pullback I.toLinearMap ∧ ∀ w,
        w ∈ (planes.plane i).map I.toLinearMap ↔ ∃ α β : ℝ, w = nativeCartanField α β 0 0 0) := by
  dsimp only
  rcases planeCount_one_four_seven_thirteen round closed proper.le with hone | hfour | hseven | hthirteen
  · omega
  · exact Or.inl ⟨by norm_num [hfour], hfour, closedPlaneSystem_complex round closed hfour i⟩
  · exact Or.inr (Or.inl ⟨by norm_num [hseven], hseven, closedPlaneSystem_quaternion round closed hseven i⟩)
  · exact Or.inr (Or.inr ⟨by norm_num [hthirteen], hthirteen, closedPlaneSystem_native round closed hthirteen i⟩)

end

end ThirteenPlanes.Peirce
