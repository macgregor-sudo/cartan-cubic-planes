module

public import ThirteenPlanes.SignedStabilizer.General
public import ThirteenPlanes.SignedStabilizer.Infinitesimal

@[expose] public section

set_option backward.privateInPublic true

/-! For every real `t ≠ 1` the cubic `c_t` of the signed model has no nonzero skew infinitesimal
symmetry, so only finitely many linear isometries of the carrier preserve it. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace SignedStabilizer

private theorem cube_ne_one {t : ℝ} (ht : t ≠ 1) : (t : ℂ) ^ 3 ≠ 1 := by
  intro h
  have h' : t ^ 3 = 1 := by exact_mod_cast h
  have hf : (t - 1) * (t ^ 2 + t + 1) = 0 := by linear_combination h'
  rcases mul_eq_zero.mp hf with h1 | h2
  · exact ht (by linarith)
  · nlinarith [sq_nonneg (t + 1 / 2)]

end SignedStabilizer

open SignedStabilizer in
/-- For real `t ≠ 1`, a skew endomorphism of the signed carrier annihilating `c_t` is zero. -/
theorem signedInteraction_skew_insert_eq_zero {t : ℝ} (ht : t ≠ 1)
    (A : SignedField →ₗ[ℝ] SignedField) (hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫)
    (hins : (interactionCubic signedPair t).insert A = 0) : A = 0 :=
  eq_zero_of_mat_eq_zero A (matrix_eq_zero (cube_ne_one ht) (insert_coefficient_eq t A hins)
    (skew_coefficient_eq A hskew))

/-- For real `t ≠ 1`, only finitely many linear isometries of the signed carrier preserve `c_t`. -/
theorem signedInteraction_stabilizer_finite {t : ℝ} (ht : t ≠ 1) :
    {g : SignedField ≃ₗᵢ[ℝ] SignedField | ∀ x y z,
      (interactionCubic signedPair t).apply (g x) (g y) (g z) =
        (interactionCubic signedPair t).apply x y z}.Finite :=
  SymmetricCubic.finite_isometry_stabilizer _
    (fun A hskew hins => signedInteraction_skew_insert_eq_zero ht A hskew hins)

end

end ThirteenPlanes
