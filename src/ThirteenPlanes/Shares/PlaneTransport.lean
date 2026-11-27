module

public import ThirteenPlanes.Shares.Responses
public import ThirteenPlanes.ClosedBlocks.Transport

@[expose] public section

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace
open PlaneContractions

noncomputable section

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {ι κ : Type*}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem planeSystem_eq_of_pointwise {P Q : PlaneDecomposition V ι} (same : ∀ i, P.plane i = Q.plane i) :
    P = Q := by
  cases P with
  | mk p _ _ _ =>
    cases Q with
    | mk q _ _ _ =>
      have he : p = q := funext same
      subst q
      rfl

/-- Reindex a complete plane system along a bijection of its indices. -/
def reindexPlaneSystem (P : PlaneDecomposition V ι) (e : κ ≃ ι) : PlaneDecomposition V κ where
  plane i := P.plane (e i)
  dimension i := P.dimension (e i)
  pairwise_orthogonal := fun _ _ he => P.pairwise_orthogonal (e.injective.ne he)
  exhaustive := e.iSup_comp.trans P.exhaustive

/-- Transport every plane back along an onto real isometry. -/
def pullbackPlaneSystem (P : PlaneDecomposition W ι) (I : V ≃ₗᵢ[ℝ] W) :
    PlaneDecomposition V ι where
  plane i := (P.plane i).map I.symm.toLinearMap
  dimension i := (mapBlockIsometry I.symm (P.plane i)).toLinearEquiv.finrank_eq.symm.trans (P.dimension i)
  pairwise_orthogonal := fun _ _ he => isOrtho_map_isometry I.symm (P.pairwise_orthogonal he)
  exhaustive := by
    rw [← Submodule.map_iSup, P.exhaustive, Submodule.map_top, LinearMap.range_eq_top.mpr I.symm.surjective]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem mem_pullbackPlaneSystem (P : PlaneDecomposition W ι) (I : V ≃ₗᵢ[ℝ] W) (i : ι) (x : V) :
    x ∈ (pullbackPlaneSystem P I).plane i ↔ I x ∈ P.plane i := by
  change x ∈ (P.plane i).map I.symm.toLinearMap ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    change I (I.symm y) ∈ P.plane i
    rw [I.apply_symm_apply]
    exact hy
  · intro hy
    exact ⟨I x, hy, I.symm_apply_apply x⟩

theorem pullbackPlaneSystem_proj (P : PlaneDecomposition W ι) (I : V ≃ₗᵢ[ℝ] W) (i : ι) (x : V) :
    I ((pullbackPlaneSystem P I).proj i x) = P.proj i (I x) := by
  apply I.symm.injective
  simp only [I.symm_apply_apply]
  change ((pullbackPlaneSystem P I).plane i).starProjection x = I.symm (P.proj i (I x))
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (mem_pullbackPlaneSystem P I i _).mpr
    rw [I.apply_symm_apply]
    exact (piP P i (I x)).property
  · intro y hy
    have hp := sub_mem_orthogonal P i (I x)
    rw [← I.inner_map_map, map_sub, I.apply_symm_apply]
    exact Submodule.inner_left_of_mem_orthogonal
      ((mem_pullbackPlaneSystem P I i y).mp hy) hp

omit [FiniteDimensional ℝ W] in
theorem IsRound.pullback_isometry {h : SymmetricCubic W} {c : ℝ} (round : IsRound h c) (I : V ≃ₗᵢ[ℝ] W) :
    IsRound (h.pullback I.toLinearMap) c := by
  refine ⟨round.positive, fun x => ?_⟩
  have hh := Peirce.pullback_intertwines_product I rfl x x
    (h := h.pullback I.toLinearMap) (k := h)
  change I ((h.pullback I.toLinearMap).squareMap x) = h.squareMap (I x) at hh
  rw [← I.norm_map ((h.pullback I.toLinearMap).squareMap x), hh, round.square_norm, I.norm_map]

omit [FiniteDimensional ℝ W] in
theorem IsClosedPlaneSystem.pullback_isometry {h : SymmetricCubic W} {P : PlaneDecomposition W ι}
    (closed : IsClosedPlaneSystem h P) (I : V ≃ₗᵢ[ℝ] W) :
    IsClosedPlaneSystem (h.pullback I.toLinearMap) (pullbackPlaneSystem P I) := by
  intro i x y hx hy
  rw [mem_pullbackPlaneSystem] at hx hy ⊢
  rw [Peirce.pullback_intertwines_product I rfl (k := h)]
  exact closed i hx hy

variable [Fintype ι]

/-- The value of the actual pencil in terms of its projected plane restrictions. -/
theorem interactionCubic_planePencil_apply (P : PlaneDecomposition V ι) (h : SymmetricCubic V)
    (t : ℝ) (x y z : V) :
    (interactionCubic (planePencil h P) t).apply x y z =
      t * h.apply x y z + (1 - t) *
        ∑ i, h.apply (P.proj i x) (P.proj i y) (P.proj i z) := by
  let D := (planePencil h P).diagonalCubic
  have hs : (h - D).apply x y z = h.apply x y z - D.apply x y z := by
    simp only [SymmetricCubic.apply, map_sub (SymmetricCubic.L (V := V)), LinearMap.sub_apply, inner_sub_left]
  rw [interactionCubic, coupling_apply, one_smul, SymmetricCubic.apply_add, SymmetricCubic.apply_smul]
  change D.apply x y z + t * (h - D).apply x y z = _
  rw [hs]
  have hD : D.apply x y z = ∑ i, h.apply (P.proj i x) (P.proj i y) (P.proj i z) := by
    dsimp only [D, planePencil]
    rw [PlaneContractions.apply_sum]
    simp only [SymmetricCubic.pullback_apply]
  rw [hD]
  ring

theorem interactionCubic_pencil_reindex [Fintype κ] (P : PlaneDecomposition V ι) (e : κ ≃ ι)
    (h : SymmetricCubic V) (t : ℝ) :
    interactionCubic (planePencil h (reindexPlaneSystem P e)) t =
      interactionCubic (planePencil h P) t := by
  apply SymmetricCubic.ext
  intro x y z
  rw [interactionCubic_planePencil_apply, interactionCubic_planePencil_apply]
  have hh : (∑ i : κ, h.apply ((reindexPlaneSystem P e).proj i x)
      ((reindexPlaneSystem P e).proj i y) ((reindexPlaneSystem P e).proj i z)) =
      ∑ i : ι, h.apply (P.proj i x) (P.proj i y) (P.proj i z) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hh]

theorem interactionCubic_pencil_pullback (P : PlaneDecomposition W ι) (I : V ≃ₗᵢ[ℝ] W)
    (h : SymmetricCubic W) (t : ℝ) :
    interactionCubic (planePencil (h.pullback I.toLinearMap) (pullbackPlaneSystem P I)) t =
      (interactionCubic (planePencil h P) t).pullback I.toLinearMap := by
  apply SymmetricCubic.ext
  intro x y z
  rw [SymmetricCubic.pullback_apply, interactionCubic_planePencil_apply, interactionCubic_planePencil_apply]
  simp only [SymmetricCubic.pullback_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, pullbackPlaneSystem_proj]

theorem normalizedPencilEnergy_pullback (P : PlaneDecomposition W ι) (I : V ≃ₗᵢ[ℝ] W)
    (h : SymmetricCubic W) (c t : ℝ) (x : V) :
    normalizedPencilEnergy (h.pullback I.toLinearMap) (pullbackPlaneSystem P I) c t x =
      normalizedPencilEnergy h P c t (I x) := by
  have hp := Peirce.pullback_intertwines_product I (interactionCubic_pencil_pullback P I h t) x x
  unfold normalizedPencilEnergy
  rw [← I.norm_map]
  change ‖I ((interactionCubic (planePencil (h.pullback I.toLinearMap) (pullbackPlaneSystem P I)) t).L x x)‖ ^ 2 / c = _
  rw [hp]
  rfl

end
end ThirteenPlanes.RoundCubics
