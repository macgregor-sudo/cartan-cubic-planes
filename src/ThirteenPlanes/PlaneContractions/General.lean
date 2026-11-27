module

public import ThirteenPlanes.Contracts

@[expose] public section

/-! Contractions of the polarized square law on an arbitrary finite-dimensional real inner-product
space: the double contraction is scalar and the triangle contraction is proportional to the cubic. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace PlaneContractions

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

open SymmetricCubic

section Basis

variable {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ W)

omit [FiniteDimensional ℝ W]

theorem expand (f : W →ₗ[ℝ] ℝ) (v : W) : f v = ∑ i, ⟪e i, v⟫ * f (e i) := by
  conv_lhs => rw [← e.sum_repr' v]
  simp [map_sum, map_smul, smul_eq_mul]

theorem expand₂ (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (u v : W) :
    B u v = ∑ i, ∑ j, B (e i) (e j) * (⟪e i, u⟫ * ⟪e j, v⟫) := by
  have h1 := expand e (B.flip v) u
  simp only [LinearMap.flip_apply] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expand e (B (e i)) v, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_inner_mul_inner' (x y : W) : ∑ i, ⟪x, e i⟫ * ⟪y, e i⟫ = ⟪x, y⟫ := by
  rw [← e.sum_inner_mul_inner x y]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm y]

theorem sum_apply_diag (g : SymmetricCubic W) (z : W) :
    ∑ i, g.apply z (e i) (e i) = LinearMap.trace ℝ W (g.L z) := by
  rw [trace_eq_sum_inner e]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem sum_inner_slices (h : SymmetricCubic W) (x y : W) :
    ∑ i, ⟪h.L x (e i), h.L y (e i)⟫ = LinearMap.trace ℝ W (h.L x * h.L y) := by
  rw [trace_eq_sum_inner e]
  exact Finset.sum_congr rfl fun i _ => h.L_isSymmetric x _ _

theorem trace_triple_eq_sum (g h : SymmetricCubic W) (x y z : W) :
    LinearMap.trace ℝ W (g.L z * h.L x * h.L y) =
      ∑ i, ∑ j, g.apply z (e i) (e j) * ⟪h.L x (e j), h.L y (e i)⟫ := by
  rw [trace_eq_sum_inner e]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_apply_eq_comp]
  rw [← g.L_isSymmetric z, ← e.sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.L_isSymmetric x]
  rfl

theorem trace_double_eq_sum (g h : SymmetricCubic W) (z w : W) :
    LinearMap.trace ℝ W (g.L z * h.L w) =
      ∑ i, ∑ j, g.apply z (e i) (e j) * h.apply w (e i) (e j) :=
  doublePair_eq_sum e g h z w

end Basis

/-- Trace-free cubics with the square law have scalar double contraction. -/
theorem trace_mul_of_squareLaw {h : SymmetricCubic W} (law : HasSquareLaw h) (tf : h.TraceFree)
    (x y : W) :
    LinearMap.trace ℝ W (h.L x * h.L y) =
      ((Module.finrank ℝ W : ℝ) + 2) / 12 * ⟪x, y⟫ := by
  let e := stdOrthonormalBasis ℝ W
  have key : ∀ i, ⟪h.L x y, h.L (e i) (e i)⟫ + 2 * ⟪h.L x (e i), h.L y (e i)⟫ =
      (⟪x, y⟫ + 2 * (⟪x, e i⟫ * ⟪y, e i⟫)) / 6 := by
    intro i
    have hp := law.polarized x y (e i) (e i)
    have hn : ⟪e i, e i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, e.orthonormal.1 i]; norm_num
    rw [hn] at hp
    linear_combination hp
  have hs := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hs
  have h0 : ∑ i, ⟪h.L x y, h.L (e i) (e i)⟫ = 0 := by
    rw [← tf (h.L x y), ← sum_apply_diag e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]
    change h.apply (e i) (e i) (h.L x y) = h.apply (h.L x y) (e i) (e i)
    rw [h.apply_swap₂₃, h.apply_swap₁₂]
  rw [h0, sum_inner_slices e, sum_inner_mul_inner' e, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_comm _ ⟪x, y⟫] at hs
  linear_combination hs / 2

/-- The doubly contracted square law, for any second cubic in the first slot. -/
theorem triangle_identity {h : SymmetricCubic W} (law : HasSquareLaw h) (g : SymmetricCubic W)
    (x y z : W) :
    2 * LinearMap.trace ℝ W (g.L z * h.L x * h.L y) +
        LinearMap.trace ℝ W (g.L z * h.L (h.L x y)) =
      (2 * g.apply z x y + LinearMap.trace ℝ W (g.L z) * ⟪x, y⟫) / 6 := by
  let e := stdOrthonormalBasis ℝ W
  set A : Fin (Module.finrank ℝ W) → Fin (Module.finrank ℝ W) → ℝ :=
    fun i j => g.apply z (e i) (e j) with hA
  have hpol : ∀ i j, 6 * (A i j * ⟪h.L x (e j), h.L y (e i)⟫ +
      A i j * h.apply (h.L x y) (e i) (e j) + A i j * ⟪h.L y (e j), h.L x (e i)⟫) =
      A i j * (⟪e i, y⟫ * ⟪e j, x⟫) + A i j * ⟪e j, e i⟫ * ⟪x, y⟫ +
        A i j * (⟪e i, x⟫ * ⟪e j, y⟫) := by
    intro i j
    have hp := law.polarized (e j) x (e i) y
    have h1 : h.apply (h.L x y) (e i) (e j) = ⟪h.L (e j) (e i), h.L x y⟫ := by
      change _ = h.apply (e j) (e i) (h.L x y)
      rw [h.apply_swap₁₂, h.apply_swap₂₃, h.apply_swap₁₂]
    rw [h1, h.L_comm x (e j), h.L_comm y (e j), h.L_comm y (e i)]
    rw [real_inner_comm (e i) x] at hp
    linear_combination 6 * A i j * hp
  have hs := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hpol i j
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have I1 := trace_triple_eq_sum e g h x y z
  have I3 : ∑ i, ∑ j, A i j * ⟪h.L y (e j), h.L x (e i)⟫ =
      ∑ i, ∑ j, A i j * ⟪h.L x (e j), h.L y (e i)⟫ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA]
    dsimp only
    rw [g.apply_swap₂₃, real_inner_comm]
  have I2 := trace_double_eq_sum e g h z (h.L x y)
  have R1 := expand₂ e (g.trilinear z) y x
  have R3 := expand₂ e (g.trilinear z) x y
  have R2 : ∑ i, ∑ j, A i j * ⟪e j, e i⟫ * ⟪x, y⟫ = LinearMap.trace ℝ W (g.L z) * ⟪x, y⟫ := by
    rw [← sum_apply_diag e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    have := expand e (g.trilinear z (e i)) (e i)
    simp only [trilinear_apply] at this
    rw [this]
    exact Finset.sum_congr rfl fun j _ => by rw [hA]; ring
  simp only [trilinear_apply] at R1 R3
  rw [I3, ← I1, ← I2, R2, ← R1, ← R3] at hs
  rw [g.apply_swap₂₃ z y x] at hs
  linear_combination hs / 6

/-- Trace-free cubics with the square law have triangle contraction proportional to the cubic. -/
theorem triangleContraction_of_squareLaw {h : SymmetricCubic W} (law : HasSquareLaw h)
    (tf : h.TraceFree) :
    h.triangleContraction = (-((Module.finrank ℝ W : ℝ) - 2) / 24) • h := by
  ext x y z
  rw [apply_triangleContraction, apply_smul]
  have hT := triangle_identity law h y z x
  rw [tf, zero_mul, add_zero, trace_mul_of_squareLaw law tf] at hT
  have h1 : ⟪x, h.L y z⟫ = h.apply x y z := by
    rw [real_inner_comm]
    change h.apply y z x = _
    rw [h.apply_swap₁₂, h.apply_swap₂₃, h.apply_swap₁₂, h.apply_swap₂₃]
  rw [h1] at hT
  linear_combination hT / 2

end PlaneContractions

end

end ThirteenPlanes
