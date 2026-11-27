module

public import ThirteenPlanes.Cubic
public import ThirteenPlanes.Planar

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The normalized square identity of the equal-strength interaction. -/
def HasSquareLaw (h : SymmetricCubic V) : Prop :=
  ∀ x : V, ‖h.squareMap x‖ ^ 2 = ‖x‖ ^ 4 / 6

namespace HasSquareLaw

private theorem inner_square {h : SymmetricCubic V} (law : HasSquareLaw h) (x : V) :
    ⟪h.L x x, h.L x x⟫ = ⟪x, x⟫ ^ 2 / 6 := by
  simpa only [real_inner_self_eq_norm_sq, ← pow_mul, Nat.reduceMul, SymmetricCubic.squareMap] using law x

private theorem pair {h : SymmetricCubic V} (law : HasSquareLaw h) (x y : V) :
    ⟪h.L x x, h.L y y⟫ + 2 * ⟪h.L x y, h.L x y⟫ =
      (⟪x, x⟫ * ⟪y, y⟫ + 2 * ⟪x, y⟫ ^ 2) / 6 := by
  have hp := law.inner_square (x + y)
  have hm := law.inner_square (x - y)
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right] at hp
  simp only [map_sub, LinearMap.sub_apply, inner_sub_left, inner_sub_right] at hm
  simp only [h.L_comm y x, real_inner_comm (h.L x x) (h.L y y), real_inner_comm x y] at hp hm
  linear_combination (hp + hm - 2 * law.inner_square x - 2 * law.inner_square y) / 4

private theorem polarizeFirst {h : SymmetricCubic V} (law : HasSquareLaw h) (w x y : V) :
    ⟪h.L w x, h.L y y⟫ + 2 * ⟪h.L w y, h.L x y⟫ =
      (⟪w, x⟫ * ⟪y, y⟫ + 2 * ⟪w, y⟫ * ⟪x, y⟫) / 6 := by
  have hp := law.pair (w + x) y
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right, h.L_comm x w,
    real_inner_comm w x, real_inner_comm (h.L w y) (h.L x y)] at hp
  linear_combination (hp - law.pair w y - law.pair x y) / 2

/-- The symmetric four-linear form determined by the square law. -/
theorem polarized {h : SymmetricCubic V} (law : HasSquareLaw h) (w x y z : V) :
    ⟪h.L w x, h.L y z⟫ + ⟪h.L w y, h.L x z⟫ + ⟪h.L w z, h.L x y⟫ =
      (⟪w, x⟫ * ⟪y, z⟫ + ⟪w, y⟫ * ⟪x, z⟫ + ⟪w, z⟫ * ⟪x, y⟫) / 6 := by
  have hp := law.polarizeFirst w x (y + z)
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right, h.L_comm z y,
    real_inner_comm y z] at hp
  linear_combination (hp - law.polarizeFirst w x y - law.polarizeFirst w x z) / 2

end HasSquareLaw

/-- Six times the squared norm of the metric-raised cubic square. -/
def unitEnergy (h : SymmetricCubic V) (x : V) : ℝ :=
  6 * ‖h.squareMap x‖ ^ 2

/-- The two trace contractions on the homogeneous coupling family. -/
structure HasContractionLaws [FiniteDimensional ℝ V] (P : CubicPair V) (lam : ℝ) : Prop where
  double : ∀ u : ℝ × ℝ,
    (coupling P u).doubleContraction = familyM lam u • (LinearMap.id : V →ₗ[ℝ] V)
  triangle : ∀ u : ℝ × ℝ,
    (coupling P u).triangleContraction = coupling P (familyP lam u, familyQ lam u)

/-- Three marked unit fields and the equal-strength square law. -/
structure EnergyTests (P : CubicPair V) (n₁ n₂ n₃ : V) : Prop where
  unit₁ : ‖n₁‖ = 1
  unit₂ : ‖n₂‖ = 1
  unit₃ : ‖n₃‖ = 1
  energy₁ : ∀ u : ℝ × ℝ, unitEnergy (coupling P u) n₁ = u.1 ^ 2
  energy₂ : ∀ u : ℝ × ℝ, unitEnergy (coupling P u) n₂ = (u.1 ^ 2 + u.2 ^ 2) / 2
  energy₃ : ∀ u : ℝ × ℝ, unitEnergy (coupling P u) n₃ = (u.1 ^ 2 + u.1 * u.2 + u.2 ^ 2) / 3
  squareLaw : HasSquareLaw (interactionCubic P 1)

/-- An indexed exhaustive orthogonal sum of real two-planes. -/
structure PlaneDecomposition (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ι : Type*) where
  plane : ι → Submodule ℝ V
  dimension : ∀ i, Module.finrank ℝ (plane i) = 2
  pairwise_orthogonal : Pairwise fun i j => (plane i).IsOrtho (plane j)
  exhaustive : ⨆ i, plane i = ⊤

variable [FiniteDimensional ℝ V]

/-- Orthogonal projection written as an endomorphism of the ambient space. -/
def PlaneDecomposition.proj {ι : Type*} (planes : PlaneDecomposition V ι) (i : ι) :
    V →ₗ[ℝ] V :=
  (planes.plane i).subtype.comp (planes.plane i).orthogonalProjectionOnto.toLinearMap

/-- Restriction of the cubic to a plane with its induced metric. -/
def PlaneDecomposition.restriction {ι : Type*} (planes : PlaneDecomposition V ι)
    (i : ι) (h : SymmetricCubic V) : SymmetricCubic (planes.plane i) :=
  h.pullback (planes.plane i).subtype

@[simp] theorem PlaneDecomposition.restriction_apply {ι : Type*} (planes : PlaneDecomposition V ι)
    (i : ι) (h : SymmetricCubic V) (x y z : planes.plane i) :
    (planes.restriction i h).apply x y z = h.apply x y z :=
  SymmetricCubic.pullback_apply h _ x y z

/-- A cubic whose diagonal part is assembled from its traceless plane restrictions. -/
structure HasPlaneData {ι : Type*} [Fintype ι] (P : CubicPair V)
    (planes : PlaneDecomposition V ι) : Prop where
  diagonal_eq : P.diagonalCubic = ∑ i, (interactionCubic P 1).pullback (planes.proj i)
  traceFree : ∀ i, (planes.restriction i (interactionCubic P 1)).TraceFree
  repeatedPlane : ∀ i (x y : planes.plane i) (z : (planes.plane i)ᗮ),
    (interactionCubic P 1).apply x y z = 0

end

end ThirteenPlanes
