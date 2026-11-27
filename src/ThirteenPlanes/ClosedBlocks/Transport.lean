module

public import ThirteenPlanes.Peirce.SlotClosedPlaneIdentification
public import ThirteenPlanes.ClosedPieces

@[expose] public section

/-! Rescaling and isometric transport of genuine cubic products and closed subspaces. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

noncomputable section

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {h : SymmetricCubic V} {k : SymmetricCubic W} {c : ℝ}

/-- Normalize a positive round strength without changing products' invariant subspaces. -/
def unitNormalize (h : SymmetricCubic V) (c : ℝ) : SymmetricCubic V := (Real.sqrt c)⁻¹ • h

omit [FiniteDimensional ℝ V] in
/-- Square law at the exact unit normalization. -/
theorem unitNormalize_isRound (round : IsRound h c) : IsRound (unitNormalize h c) 1 := by
  let s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.mpr round.positive
  have hsq : (s⁻¹) ^ 2 * c = 1 := by
    rw [inv_pow, show s ^ 2 = c from Real.sq_sqrt round.positive.le,
      inv_mul_cancel₀ round.positive.ne']
  refine ⟨by norm_num, fun x => ?_⟩
  change ‖(s⁻¹ • h).squareMap x‖ ^ 2 = _
  rw [SymmetricCubic.squareMap_smul, norm_smul, mul_pow, Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
    round.square_norm, ← mul_assoc, hsq, one_mul]

omit [FiniteDimensional ℝ V] in
theorem eq_smul_unitNormalize (round : IsRound h c) : h = Real.sqrt c • unitNormalize h c := by
  rw [unitNormalize, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr round.positive).ne', one_smul]

omit [FiniteDimensional ℝ V] in
/-- Closed subspaces are unchanged by nonzero scalar rescaling. -/
theorem isClosedPiece_smul_iff {s : ℝ} (hs : s ≠ 0) (U : Submodule ℝ V) :
    IsClosedPiece (s • h) U ↔ IsClosedPiece h U := by
  constructor
  · intro hh x y hx hy
    have hxy : s • h.L x y ∈ U := by
      simpa only [map_smul, LinearMap.smul_apply] using hh hx hy
    simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using U.smul_mem s⁻¹ hxy
  · intro hh x y hx hy
    simpa only [map_smul, LinearMap.smul_apply] using U.smul_mem s (hh hx hy)

omit [FiniteDimensional ℝ V] in
theorem unitNormalize_traceFree (tf : h.TraceFree) : (unitNormalize h c).TraceFree := by
  intro x
  change LinearMap.trace ℝ V (((Real.sqrt c)⁻¹ • h).L x) = 0
  rw [map_smul, LinearMap.smul_apply, map_smul, tf x, smul_zero]

omit [FiniteDimensional ℝ V] in
/-- An onto isometry transports the actual orthogonality of subspaces. -/
theorem isOrtho_map_isometry (I : V ≃ₗᵢ[ℝ] W) {U S : Submodule ℝ V} (ho : U.IsOrtho S) :
    (U.map I.toLinearMap).IsOrtho (S.map I.toLinearMap) := by
  apply Submodule.isOrtho_iff_inner_eq.mpr
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  change ⟪I x, I y⟫ = 0
  rw [I.inner_map_map, ho.inner_eq hx hy]

/-- An onto cubic isometry transports closure under the actual product. -/
theorem isClosedPiece_map_isometry (I : V ≃ₗᵢ[ℝ] W) (hI : h = k.pullback I.toLinearMap)
    {U : Submodule ℝ V} (closed : IsClosedPiece h U) : IsClosedPiece k (U.map I.toLinearMap) := by
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  refine ⟨h.L x y, closed hx hy, ?_⟩
  exact Peirce.pullback_intertwines_product I hI x y

/-- The induced isometry between a block and its image under an ambient isometry. -/
def mapBlockIsometry (I : V ≃ₗᵢ[ℝ] W) (U : Submodule ℝ V) : U ≃ₗᵢ[ℝ] U.map I.toLinearMap :=
  ⟨Submodule.equivMapOfInjective I.toLinearMap I.injective U, fun x => I.norm_map x⟩

omit [FiniteDimensional ℝ V] in
@[simp] theorem mapBlockIsometry_coe (I : V ≃ₗᵢ[ℝ] W) (U : Submodule ℝ V) (x : U) :
    ((mapBlockIsometry I U x : U.map I.toLinearMap) : W) = I x := rfl


/-- Pullback commutes with rescaling a cubic. -/
theorem pullback_smul_cubic (g : SymmetricCubic W) (f : V →ₗ[ℝ] W) (t : ℝ) :
    (t • g).pullback f = t • g.pullback f := by
  apply SymmetricCubic.ext
  intro x y z
  simp only [SymmetricCubic.pullback_apply, SymmetricCubic.apply_smul]

omit [FiniteDimensional ℝ V] in
/-- Any nonzero scaling preserves trace-freeness. -/
theorem traceFree_smul_iff (g : SymmetricCubic V) {t : ℝ} (ht : t ≠ 0) :
    (t • g).TraceFree ↔ g.TraceFree := by
  constructor
  · intro h x
    have hx := h x
    rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul] at hx
    exact (mul_eq_zero.mp hx).resolve_left ht
  · intro h x
    rw [map_smul, LinearMap.smul_apply, map_smul, h x, smul_zero]

/-- An onto cubic isometry preserves trace-freeness by conjugating the multiplication maps. -/
theorem traceFree_pullback_iff (g : SymmetricCubic W) (I : V ≃ₗᵢ[ℝ] W) :
    (g.pullback I.toLinearMap).TraceFree ↔ g.TraceFree := by
  have ht (x : V) :
      LinearMap.trace ℝ V ((g.pullback I.toLinearMap).L x) =
        LinearMap.trace ℝ W (g.L (I x)) := by
    have hc : I.toLinearEquiv.conj ((g.pullback I.toLinearMap).L x) = g.L (I x) := by
      apply LinearMap.ext
      intro y
      change I ((g.pullback I.toLinearMap).L x (I.symm y)) = g.L (I x) y
      rw [Peirce.pullback_intertwines_product I rfl, I.apply_symm_apply]
    rw [← hc, LinearMap.trace_conj']
  exact ⟨fun h y => by
    obtain ⟨x, rfl⟩ := I.surjective y
    rw [← ht]
    exact h x,
    fun h x => (ht x).trans (h (I x))⟩

/-- Restricting and then transporting gives the restriction to the actual image block. -/
theorem pullback_block_map (g : SymmetricCubic W) (I : V ≃ₗᵢ[ℝ] W) (U : Submodule ℝ V) :
    (g.pullback I.toLinearMap).pullback U.subtype =
      (g.pullback (U.map I.toLinearMap).subtype).pullback (mapBlockIsometry I U).toLinearMap := by
  apply SymmetricCubic.ext
  intro x y z
  simp only [SymmetricCubic.pullback_apply]
  rfl

end

end ThirteenPlanes.RoundCubics
