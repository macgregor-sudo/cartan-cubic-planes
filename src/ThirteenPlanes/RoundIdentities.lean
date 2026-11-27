module

public import ThirteenPlanes.Basic
public import ThirteenPlanes.PlaneContractions.General

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {h : SymmetricCubic V} {c : ℝ}

private theorem normalize (round : IsRound h c) :
    ∃ (s : ℝ) (g : SymmetricCubic V), s ^ 2 = 6 * c ∧ h = s • g ∧
      HasSquareLaw g ∧ s ≠ 0 := by
  let s := Real.sqrt (6 * c)
  have hc := round.positive
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 6 * c := Real.sq_sqrt (by positivity)
  refine ⟨s, s⁻¹ • h, hs2, ?_, ?_, hs.ne'⟩
  · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  · intro x
    have hscale : s⁻¹ ^ 2 * c = 1 / 6 := by
      rw [inv_pow, hs2]
      field_simp
    rw [SymmetricCubic.squareMap_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hs.le), mul_pow, round.square_norm, ← mul_assoc, hscale]
    ring

theorem polarized (round : IsRound h c) (x y z w : V) :
    ⟪h.L x y, h.L z w⟫ + ⟪h.L x z, h.L y w⟫ + ⟪h.L x w, h.L y z⟫ =
      c * (⟪x, y⟫ * ⟪z, w⟫ + ⟪x, z⟫ * ⟪y, w⟫ + ⟪x, w⟫ * ⟪y, z⟫) := by
  obtain ⟨s, g, hs2, hh, law, _⟩ := normalize round
  calc
    _ = s ^ 2 * (⟪g.L x y, g.L z w⟫ + ⟪g.L x z, g.L y w⟫ + ⟪g.L x w, g.L y z⟫) := by
      rw [hh]
      simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right]
      ring
    _ = _ := by rw [law.polarized, hs2]; ring

theorem pair (round : IsRound h c) (x z : V) :
    ⟪h.L x x, h.L z z⟫ + 2 * ‖h.L x z‖ ^ 2 =
      c * (‖x‖ ^ 2 * ‖z‖ ^ 2 + 2 * ⟪x, z⟫ ^ 2) := by
  have hp := polarized round x x z z
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hp
  linear_combination hp

variable [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
private theorem sum_slice_sq (round : IsRound h c) (tf : h.TraceFree)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) :
    (∑ i, (h.L (e i)) ^ 2) = (c * ((Module.finrank ℝ V : ℝ) + 2) / 2) •
      (1 : Module.End ℝ V) := by
  classical
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  have key (i : ι) : ⟪h.L (e i) (e i), h.L x y⟫ +
      2 * ⟪h.L (e i) x, h.L (e i) y⟫ =
      c * (⟪x, y⟫ + 2 * (⟪e i, x⟫ * ⟪e i, y⟫)) := by
    have hp := polarized round (e i) (e i) x y
    have hunit : ⟪e i, e i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, e.orthonormal.1 i]
      norm_num
    rw [hunit, real_inner_comm (h.L (e i) x) (h.L (e i) y)] at hp
    linear_combination hp
  have hs := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hz : ∑ i, ⟪h.L (e i) (e i), h.L x y⟫ = 0 := by
    rw [← tf (h.L x y), ← PlaneContractions.sum_apply_diag e]
    refine Finset.sum_congr rfl fun i _ => ?_
    change h.apply (e i) (e i) (h.L x y) = h.apply (h.L x y) (e i) (e i)
    rw [h.apply_swap₂₃, h.apply_swap₁₂]
  have he : ∑ i, ⟪e i, x⟫ * ⟪e i, y⟫ = ⟪x, y⟫ := by
    rw [← e.sum_inner_mul_inner x y]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm x]
  have hsym : ∑ i, ⟪h.L (e i) x, h.L (e i) y⟫ =
      ⟪(∑ i, (h.L (e i)) ^ 2) x, y⟫ := by
    rw [LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_two]
    exact (h.L_isSymmetric (e i) (h.L (e i) x) y).symm
  rw [hz, hsym, he, Finset.sum_const, Finset.card_univ, ← Module.finrank_eq_card_basis e.toBasis,
    nsmul_eq_mul] at hs
  simp only [LinearMap.smul_apply, one_apply_eq_self, real_inner_smul_left]
  linear_combination hs / 2

private theorem trace_slice_cube (round : IsRound h c) (tf : h.TraceFree) (x : V) :
    LinearMap.trace ℝ V ((h.L x) ^ 3) =
      -(c * ((Module.finrank ℝ V : ℝ) - 2) / 4) * h.apply x x x := by
  obtain ⟨s, g, hs2, hh, law, hs⟩ := normalize round
  have hL (v : V) : h.L v = s • g.L v := by
    simp only [hh, map_smul, LinearMap.smul_apply]
  have tg : g.TraceFree := by
    intro v
    have ht := tf v
    rw [hL, map_smul, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left hs
  have ht := congrArg (fun f : SymmetricCubic V => f.apply x x x)
    (PlaneContractions.triangleContraction_of_squareLaw law tg)
  simp only [SymmetricCubic.apply_triangleContraction, SymmetricCubic.apply_smul,
    ← pow_succ, ← pow_two] at ht
  calc
    _ = s ^ 3 * LinearMap.trace ℝ V ((g.L x) ^ 3) := by
      rw [hL, smul_pow, map_smul, smul_eq_mul]
    _ = _ := by
      rw [ht, hh, SymmetricCubic.apply_smul, pow_succ, hs2]
      ring

/-- The polarized round identities, with harmonicity expressed by the trace-free slices. -/
theorem polarization_and_contractions (round : IsRound h c) :
    (∀ x y z w : V,
      ⟪h.L x y, h.L z w⟫ + ⟪h.L x z, h.L y w⟫ + ⟪h.L x w, h.L y z⟫ =
        c * (⟪x, y⟫ * ⟪z, w⟫ + ⟪x, z⟫ * ⟪y, w⟫ + ⟪x, w⟫ * ⟪y, z⟫)) ∧
    (∀ x z : V, ⟪h.L x x, h.L z z⟫ + 2 * ‖h.L x z‖ ^ 2 =
        c * (‖x‖ ^ 2 * ‖z‖ ^ 2 + 2 * ⟪x, z⟫ ^ 2)) ∧
    (h.TraceFree →
      (∀ {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V),
        (∑ i, (h.L (e i)) ^ 2) = (c * ((Module.finrank ℝ V : ℝ) + 2) / 2) •
          (1 : Module.End ℝ V)) ∧
      (∀ x : V, LinearMap.trace ℝ V ((h.L x) ^ 3) =
        -(c * ((Module.finrank ℝ V : ℝ) - 2) / 4) * h.apply x x x)) := by
  exact ⟨polarized round, pair round, fun tf => ⟨sum_slice_sq round tf, trace_slice_cube round tf⟩⟩

end ThirteenPlanes.RoundCubics
