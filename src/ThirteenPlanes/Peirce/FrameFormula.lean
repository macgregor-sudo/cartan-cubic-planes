module

public import ThirteenPlanes.PeirceDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! The printed frame formula, using the full unital product and its trace-zero part. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

variable {V J : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- An ordered trace-one Jordan frame for the metric product and specified unit. -/
structure TraceJordanFrame (g : SymmetricCubic J) (e : J) (p : Fin 3 → J) : Prop where
  trace_one : ∀ i, ⟪e, p i⟫ = 1
  idempotent : ∀ i, g.L (p i) (p i) = p i
  orthogonal : ∀ i j, i ≠ j → g.L (p i) (p j) = 0
  sum_unit : ∑ i, p i = e

/-- The literal formula of Lemma 2b-frames. -/
def framePoint (F : V →ₗᵢ[ℝ] J) (e : J) (a : V) : J :=
  (1 / 3 : ℝ) • (e + Real.sqrt 6 • F a)

private theorem unitIdempotent_pair (h : SymmetricCubic V) (x y z : V)
    (hx : IsUnitIdempotent h x) (hy : IsUnitIdempotent h y) (hz : IsUnitIdempotent h z)
    (hsum : x + y + z = 0) : h.L x y = -(x + y) ∧ ⟪x, y⟫ = -(1 / 2 : ℝ) := by
  have hxy : x + y = -z := eq_neg_of_add_eq_zero_left hsum
  have hsq : h.L (x + y) (x + y) = z := by
    rw [hxy]
    simp [hz.square_eq_self]
  simp only [map_add, LinearMap.add_apply, hx.square_eq_self, hy.square_eq_self, h.L_comm y x] at hsq
  constructor
  · have hs := congrArg ((1 / 2 : ℝ) • ·) (hsq.trans (neg_eq_iff_eq_neg.mpr hxy).symm)
    linear_combination (norm := module) hs
  · have hn := norm_add_sq_real x y
    rw [hxy, norm_neg, hx.norm_eq_one, hy.norm_eq_one, hz.norm_eq_one] at hn
    linarith only [hn]

private theorem unitIdempotent_three_pairs {h : SymmetricCubic V} {a : Fin 3 → V}
    (ha : ∀ i, IsUnitIdempotent h (a i)) (hs : ∑ i, a i = 0) (i j : Fin 3) (hij : i ≠ j) :
    h.L (a i) (a j) = -(a i + a j) ∧ ⟪a i, a j⟫ = -(1 / 2 : ℝ) := by
  have hc (i j k : Fin 3) (hs' : a i + a j + a k = 0) := unitIdempotent_pair h _ _ _ (ha i) (ha j) (ha k) hs'
  rw [Fin.sum_univ_three] at hs
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hc 0 1 2 hs
  · exact hc 0 2 1 (by linear_combination (norm := abel) hs)
  · exact hc 1 0 2 (by linear_combination (norm := abel) hs)
  · exact (hij rfl).elim
  · exact hc 1 2 0 (by linear_combination (norm := abel) hs)
  · exact hc 2 0 1 (by linear_combination (norm := abel) hs)
  · exact hc 2 1 0 (by linear_combination (norm := abel) hs)
  · exact (hij rfl).elim

/-- The three unit idempotents yield the actual normalized Jordan frame in the full model. The
product equality is the raw product split into its centered part and its scalar trace component. -/
theorem frame_of_three_unit_idempotents (h : SymmetricCubic V) (g : SymmetricCubic J) (e : J)
    (F : V →ₗᵢ[ℝ] J) (unit : ∀ x, g.L e x = x) (rank : ⟪e, e⟫ = 3)
    (tf : ∀ x, ⟪e, F x⟫ = 0)
    (product : ∀ x y, g.L (F x) (F y) = (Real.sqrt 6)⁻¹ • F (h.L x y) + (⟪x, y⟫ / 3) • e)
    (a : Fin 3 → V) (ha : ∀ i, IsUnitIdempotent h (a i)) (hs : ∑ i, a i = 0) :
    TraceJordanFrame g e (fun i => framePoint F e (a i)) := by
  let s := Real.sqrt 6
  have hs₂ : s ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have mult (x y : V) :
      g.L (framePoint F e x) (framePoint F e y) = (1 / 9 : ℝ) •
        ((1 + 2 * ⟪x, y⟫) • e + s • (F x + F y + F (h.L x y))) := by
    change g.L ((1 / 3 : ℝ) • (e + s • F x)) ((1 / 3 : ℝ) • (e + s • F y)) = _
    have unit_right (z : J) : g.L z e = z := (g.L_comm z e).trans (unit z)
    have hproduct : g.L (F x) (F y) = s⁻¹ • F (h.L x y) + (⟪x, y⟫ / 3) • e := product x y
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      unit, unit_right, hproduct, smul_add, smul_smul]
    match_scalars <;> ring_nf
    · rw [hs₂]
      ring
    · have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne'
      rw [pow_two, mul_assoc s s s⁻¹, hsi, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [framePoint, real_inner_smul_right, inner_add_right, rank, real_inner_smul_right, tf]
    ring
  · intro i
    rw [mult, (ha i).square_eq_self, real_inner_self_eq_norm_sq, (ha i).norm_eq_one]
    change (1 / 9 : ℝ) • ((1 + 2 * 1 ^ 2) • e + s • (F (a i) + F (a i) + F (a i))) =
      (1 / 3 : ℝ) • (e + s • F (a i))
    module
  · intro i j hij
    obtain ⟨hp, hi⟩ := unitIdempotent_three_pairs ha hs i j hij
    rw [mult, hp, hi, map_neg, map_add]
    module
  · have hsf : ∑ i, F (a i) = 0 := by rw [← map_sum, hs, map_zero]
    change (∑ i, (1 / 3 : ℝ) • (e + s • F (a i))) = e
    rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum, hsf, smul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    module

/-- Orthogonal source planes give trace overlap `1/3` for every pair of the printed frame points. -/
theorem framePoint_inner_of_orthogonal (F : V →ₗᵢ[ℝ] J) (e : J) (rank : ⟪e, e⟫ = 3)
    (tf : ∀ x, ⟪e, F x⟫ = 0) {x y : V} (orth : ⟪x, y⟫ = 0) :
    ⟪framePoint F e x, framePoint F e y⟫ = 1 / 3 := by
  have hft : ⟪F x, e⟫ = 0 := (real_inner_comm _ _).trans (tf x)
  simp only [framePoint, real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    rank, tf, hft, F.inner_map_map, orth]
  ring

end

end ThirteenPlanes.Peirce
