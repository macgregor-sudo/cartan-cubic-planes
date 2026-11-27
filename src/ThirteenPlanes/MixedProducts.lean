module

public import ThirteenPlanes.RoundIdentities

@[expose] public section

set_option backward.privateInPublic true

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {h : SymmetricCubic V} {c : ℝ} {U U' : Submodule ℝ V}

private theorem mixed_mem_left (orth : U.IsOrtho U') (closed : IsClosedPiece h U)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U') : h.L x y ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  change h.apply x y u = 0
  rw [h.apply_swap₂₃]
  exact orth.inner_eq (closed hx hu) hy

private theorem mixed_mem (orth : U.IsOrtho U') (closed : IsClosedPiece h U)
    (closed' : IsClosedPiece h U') {x y : V} (hx : x ∈ U) (hy : y ∈ U') :
    h.L x y ∈ (U ⊔ U')ᗮ := by
  rw [← Submodule.inf_orthogonal]
  refine ⟨mixed_mem_left orth closed hx hy, ?_⟩
  rw [h.L_comm]
  exact mixed_mem_left orth.symm closed' hy hx

private theorem mixed_norm (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    {x y : V} (hx : x ∈ U) (hy : y ∈ U') :
    2 * ‖h.L x y‖ ^ 2 = c * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hp := pair round x y
  rw [orth.inner_eq (closed hx hx) (closed' hy hy), orth.inner_eq hx hy] at hp
  linear_combination hp

variable [FiniteDimensional ℝ V]

private theorem mixed_finrank_le (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U') (hU : U ≠ ⊥) :
    Module.finrank ℝ U' ≤ Module.finrank ℝ (U ⊔ U')ᗮ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  let f : U' →ₗ[ℝ] (U ⊔ U')ᗮ := ((h.L x).comp U'.subtype).codRestrict _ fun y =>
    mixed_mem orth closed closed' hx y.property
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have hzero : h.L x (y : V) = 0 := congrArg Subtype.val hy
  have hn := mixed_norm round orth closed closed' hx y.property
  apply Subtype.ext
  by_contra hy0
  have hpos : 0 < c * ‖x‖ ^ 2 * ‖(y : V)‖ ^ 2 := by
    exact mul_pos (mul_pos round.positive (pow_pos (norm_pos_iff.2 hx0) _))
      (pow_pos (norm_pos_iff.2 hy0) _)
  rw [hzero, norm_zero] at hn
  linarith

/-- The mixed product law in mixed product law. -/
theorem mixedProductLaw (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U') :
    (∀ ⦃x y : V⦄, x ∈ U → y ∈ U' →
      h.L x y ∈ (U ⊔ U')ᗮ ∧ 2 * ‖h.L x y‖ ^ 2 = c * ‖x‖ ^ 2 * ‖y‖ ^ 2) ∧
    (U ≠ ⊥ → U' ≠ ⊥ →
      Module.finrank ℝ U + Module.finrank ℝ U' +
        max (Module.finrank ℝ U) (Module.finrank ℝ U') ≤ Module.finrank ℝ V) := by
  refine ⟨fun {_ _} hx hy => ⟨mixed_mem orth closed closed' hx hy,
    mixed_norm round orth closed closed' hx hy⟩, ?_⟩
  intro hU hU'
  have hright := mixed_finrank_le round orth closed closed' hU
  have hleft := mixed_finrank_le round orth.symm closed' closed hU'
  rw [sup_comm U' U] at hleft
  have hmax := max_le hleft hright
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U U'
  rw [orth.disjoint.eq_bot, finrank_bot, add_zero] at hsum
  rw [← hsum, ← Submodule.finrank_add_finrank_orthogonal (U ⊔ U')]
  exact Nat.add_le_add_left hmax _

end ThirteenPlanes.RoundCubics
