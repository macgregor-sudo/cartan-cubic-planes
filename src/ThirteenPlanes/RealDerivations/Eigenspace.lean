module

public import ThirteenPlanes.RealDerivations.Lift
public import ThirteenPlanes.RealDerivations.Representation

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RealDerivations

open Peirce Polynomial
open scoped RealInnerProductSpace

noncomputable section

private theorem positive_gram_rootMultiplicity (q t : ℝ) (ht : 0 < t) :
    (X * (X - C q) ^ 2 * (X - C (4 * q)) ^ 2 : ℝ[X]).rootMultiplicity t ≤ 2 := by
  let p : ℝ[X] := X - C q
  let r : ℝ[X] := X - C (4 * q)
  have hp : p ≠ 0 := X_sub_C_ne_zero q
  have hr : r ≠ 0 := X_sub_C_ne_zero (4*q)
  have hz : (X : ℝ[X]).rootMultiplicity t = 0 :=
    rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot, ht.ne'])
  have hfactor (v : ℝ) (hv : t ≠ v) : ((X - C v) ^ 2 : ℝ[X]).rootMultiplicity t = 0 :=
    rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot, sub_ne_zero.mpr hv])
  change (X * p ^ 2 * r ^ 2).rootMultiplicity t ≤ 2
  rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero X_ne_zero (pow_ne_zero _ hp)) (pow_ne_zero _ hr)),
    rootMultiplicity_mul (mul_ne_zero X_ne_zero (pow_ne_zero _ hp)), hz, zero_add]
  by_cases hq : t = q
  · have h4 : t ≠ 4*q := by rw [← hq]; linarith
    rw [show (p ^ 2).rootMultiplicity t = 2 by rw [hq]; exact rootMultiplicity_X_sub_C_pow q 2,
      hfactor _ h4]
  · rw [hfactor _ hq, zero_add]
    by_cases h4 : t = 4*q
    · rw [h4]
      exact le_of_eq (rootMultiplicity_X_sub_C_pow (4*q) 2)
    · rw [hfactor _ h4]
      decide

/-- A positive squared singular value of a skew derivation on the actual five-dimensional
real trace space has eigenspace dimension at most two. -/
theorem realTraceDerivation_gram_eigenspace_finrank_le_two
    (D : Module.End ℝ RealTracelessSymmetric3)
    (hd : ∀ x y, D (realCartanCubic.L x y) = realCartanCubic.L (D x) y + realCartanCubic.L x (D y))
    (hs : ∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫) (t : ℝ) (ht : 0 < t) :
    Module.finrank ℝ (LinearMap.ker ((traceAdjoint D).comp D - t • LinearMap.id)) ≤ 2 := by
  obtain ⟨T, hT, hD⟩ := realTraceDerivation_inner D hd hs
  have he := LinearMap.finrank_eigenspace_le ((traceAdjoint D).comp D) t
  rw [Module.End.eigenspace_def, actual_commutatorGram_charpoly hT hD hs] at he
  exact he.trans (positive_gram_rootMultiplicity _ t ht)

end

end ThirteenPlanes.RealDerivations
