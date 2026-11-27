module

public import ThirteenPlanes.Peirce.SlotModelIdentification
public import ThirteenPlanes.Peirce.SlotQuaternionIdentification

@[expose] public section

set_option backward.privateInPublic true

/-! The marked isometries carry the selected closed plane onto the traceless diagonals. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open Submodule

variable {V W ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {h : SymmetricCubic V} {k : SymmetricCubic W}
  {planes : PlaneDecomposition V ι} {a : V} {b : minusSpace h a}

/-- A cubic pullback by an onto isometry intertwines the actual multiplication. -/
theorem pullback_intertwines_product (I : V ≃ₗᵢ[ℝ] W) (hh : h = k.pullback I.toLinearMap)
    (x y : V) : I (h.L x y) = k.L (I x) (I y) := by
  apply ext_inner_right ℝ
  intro z
  obtain ⟨w, rfl⟩ := I.surjective z
  rw [I.inner_map_map]
  change h.apply x y w = k.apply (I x) (I y) (I w)
  rw [hh, SymmetricCubic.pullback_apply]
  rfl

private theorem selectedPlane_eq_markedSpan (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    (hb : ‖b‖ = 1) (i : ι) (hai : a ∈ planes.plane i) (hbi : (b : V) ∈ planes.plane i) :
    planes.plane i = (ℝ ∙ a) ⊔ (ℝ ∙ (b : V)) := by
  symm
  have hs₁ : (ℝ ∙ a) ≤ planes.plane i := span_le.mpr (Set.singleton_subset_iff.mpr hai)
  have hs₂ : (ℝ ∙ (b : V)) ≤ planes.plane i := span_le.mpr (Set.singleton_subset_iff.mpr hbi)
  apply Submodule.eq_of_le_of_finrank_le (sup_le hs₁ hs₂)
  rw [planes.dimension, (markedPlane_normalForm round ha hb).2.2.2.1]

omit [FiniteDimensional ℝ V] in
private theorem image_span_iff (I : V ≃ₗᵢ[ℝ] W) (a b : V) (w : W) :
    w ∈ ((ℝ ∙ a) ⊔ (ℝ ∙ b)).map I.toLinearMap ↔
      ∃ α β : ℝ, w = α • I a + β • I b := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup.mp hv
    obtain ⟨α, rfl⟩ := mem_span_singleton.mp hx
    obtain ⟨β, rfl⟩ := mem_span_singleton.mp hy
    exact ⟨α, β, by simp⟩
  · rintro ⟨α, β, rfl⟩
    refine ⟨α • a + β • b, ?_, by simp⟩
    exact mem_sup.mpr ⟨_, smul_mem _ _ (mem_span_singleton_self a),
      _, smul_mem _ _ (mem_span_singleton_self b), rfl⟩

private theorem linear_markedCoordinates {K : Type*} [AddCommGroup K] [Module ℝ K]
    (e : (ℝ × ℝ × K × K × K) ≃ₗ[ℝ] W) (α β : ℝ) :
    α • e (1, 0, 0, 0, 0) + β • e (0, 1, 0, 0, 0) = e (α, β, 0, 0, 0) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  exact Prod.ext (by simp) (Prod.ext (by simp) (by simp))

/-- The four-plane branch of Theorem 2b-ident, with any selected plane marked. -/
theorem closedPlaneSystem_complex [Fintype ι]
    (round : IsRound h 1) (closed : IsClosedPlaneSystem h planes)
    (hm : Fintype.card ι = 4) (i : ι) :
    ∃ I : V ≃ₗᵢ[ℝ] TracelessHermitian3,
      h = complexCartanCubic.pullback I.toLinearMap ∧
      ∀ w, w ∈ (planes.plane i).map I.toLinearMap ↔
        ∃ α β : ℝ, w = complexCartanField α β 0 0 0 := by
  obtain ⟨a, b, hai, hbi, ha, hb⟩ := markedPair_of_closed_plane round closed i
  have hd : Module.finrank ℝ V = 8 := by rw [finrank_eq_twice_card planes, hm]
  obtain ⟨I, hIa, hIb, hI⟩ := markedRoundCubic_complex round ha hb
    (RoundCubics.traceFree_of_isClosedPlaneSystem round closed a) hd
  refine ⟨I, hI, fun w => ?_⟩
  rw [selectedPlane_eq_markedSpan round ha hb i hai hbi]
  refine (image_span_iff I a (b : V) w).trans ?_
  rw [hIa, hIb]
  simp only [← complexCartanEquiv_apply]
  simp only [linear_markedCoordinates (W := TracelessHermitian3) (K := ℂ) complexCartanEquiv]

open scoped Quaternion in
/-- The seven-plane branch of Theorem 2b-ident, with any selected plane marked. -/
theorem closedPlaneSystem_quaternion [Fintype ι]
    (round : IsRound h 1) (closed : IsClosedPlaneSystem h planes)
    (hm : Fintype.card ι = 7) (i : ι) :
    ∃ I : V ≃ₗᵢ[ℝ] QuaternionicMUB.TracelessHilbert,
      h = quaternionCartanCubic.pullback I.toLinearMap ∧
      ∀ w, w ∈ (planes.plane i).map I.toLinearMap ↔
        ∃ α β : ℝ, w = quaternionCartanField α β 0 0 0 := by
  obtain ⟨a, b, hai, hbi, ha, hb⟩ := markedPair_of_closed_plane round closed i
  have hd : Module.finrank ℝ V = 14 := by rw [finrank_eq_twice_card planes, hm]
  obtain ⟨I, hIa, hIb, hI⟩ := markedRoundCubic_quaternion round ha hb
    (RoundCubics.traceFree_of_isClosedPlaneSystem round closed a) hd
  refine ⟨I, hI, fun w => ?_⟩
  rw [selectedPlane_eq_markedSpan round ha hb i hai hbi]
  refine (image_span_iff I a (b : V) w).trans ?_
  rw [hIa, hIb]
  simp only [← quaternionCartanEquiv_apply]
  simp only [linear_markedCoordinates (W := QuaternionicMUB.TracelessHilbert) (K := Quaternion ℝ) quaternionCartanEquiv]

open scoped ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean in
/-- The thirteen-plane branch of Theorem 2b-ident, with any selected plane marked. -/
theorem closedPlaneSystem_native [Fintype ι]
    (round : IsRound h 1) (closed : IsClosedPlaneSystem h planes)
    (hm : Fintype.card ι = 13) (i : ι) :
    ∃ I : V ≃ₗᵢ[ℝ] NativeTraceless,
      h = nativeCartanCubic.pullback I.toLinearMap ∧
      ∀ w, w ∈ (planes.plane i).map I.toLinearMap ↔
        ∃ α β : ℝ, w = nativeCartanField α β 0 0 0 := by
  obtain ⟨a, b, hai, hbi, ha, hb⟩ := markedPair_of_closed_plane round closed i
  have hd : Module.finrank ℝ V = 26 := by rw [finrank_eq_twice_card planes, hm]
  obtain ⟨I, hIa, hIb, hI⟩ := markedRoundCubic_native round ha hb
    (RoundCubics.traceFree_of_isClosedPlaneSystem round closed a) hd
  refine ⟨I, hI, fun w => ?_⟩
  rw [selectedPlane_eq_markedSpan round ha hb i hai hbi]
  refine (image_span_iff I a (b : V) w).trans ?_
  rw [hIa, hIb]
  simp only [← nativeCartanEquiv_apply, linear_markedCoordinates]

end

end ThirteenPlanes.Peirce
