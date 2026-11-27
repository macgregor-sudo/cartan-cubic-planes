module

public import ThirteenPlanes.Peirce.UnitIdempotent
public import ThirteenPlanes.ClosedBlocks.Transport

@[expose] public section

set_option backward.privateInPublic true

/-! The three unit idempotents of a normalized closed plane. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open RoundCubics

private def trianglePoint (i : Fin 3) : ℂ :=
  ![1, ⟨-1 / 2, Real.sqrt 3 / 2⟩, ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩] i

private theorem trianglePoint_norm (i : Fin 3) : ‖trianglePoint i‖ = 1 := by
  have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  fin_cases i <;> norm_num [trianglePoint] <;> nlinarith

private theorem trianglePoint_cube_re (i : Fin 3) : ((trianglePoint i) ^ 3).re = 1 := by
  have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> norm_num [trianglePoint, pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith

private theorem trianglePoint_sum : ∑ i, trianglePoint i = 0 := by
  rw [Fin.sum_univ_three]
  apply Complex.ext <;> norm_num [trianglePoint]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Three norm-one idempotents in any normalized closed plane, with zero sum. -/
theorem closedPlane_three_unitIdempotents {h : SymmetricCubic V} (round : IsRound h 1)
    (S : Submodule ℝ V) (dim : Module.finrank ℝ S = 2) (closed : IsClosedPiece h S) :
    ∃ a : Fin 3 → V, (∀ i, a i ∈ S) ∧ (∀ i, IsUnitIdempotent h (a i)) ∧ ∑ i, a i = 0 := by
  let g := h.pullback S.subtype
  have hr : IsRound g 1 := closedSubspace_restriction_isRound round closed
  obtain ⟨_, z, hz⟩ := binaryPlaneNormalForm hr dim
  let a (i : Fin 3) := z.symm (trianglePoint i)
  have ha (i : Fin 3) : ‖a i‖ = 1 := by rw [show a i = _ from rfl, z.symm.norm_map, trianglePoint_norm]
  have hui (i : Fin 3) : IsUnitIdempotent g (a i) := by
    apply unitIdempotent_of_isMaxOn g hr
    · simpa using ha i
    · intro x hx
      have hn : ‖x‖ = 1 := by simpa using hx
      change g.apply x x x ≤ g.apply (a i) (a i) (a i)
      rw [hz, hz, show z (a i) = trianglePoint i from z.apply_symm_apply _, trianglePoint_cube_re,
        Real.sqrt_one, one_mul, one_mul]
      calc
        _ ≤ ‖(z x)^3‖ := Complex.re_le_norm _
        _ = 1 := by rw [norm_pow, z.norm_map, hn, one_pow]
  have hsum : (∑ i, a i) = 0 := by
    change (∑ i, z.symm (trianglePoint i)) = 0
    rw [← map_sum, trianglePoint_sum, map_zero]
  refine ⟨fun i => (a i : V), fun i => (a i).property, ?_, ?_⟩
  · intro i
    refine ⟨(hui i).norm_eq_one, ?_⟩
    rw [← closedSubspace_restriction_product closed (a i) (a i), (hui i).square_eq_self]
  · change (∑ i, S.subtype (a i)) = 0
    rw [← map_sum, hsum, map_zero]

end

end ThirteenPlanes.Peirce
