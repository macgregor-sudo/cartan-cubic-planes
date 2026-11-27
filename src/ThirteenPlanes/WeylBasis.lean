module

public import ThirteenPlanes.Weyl
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace ThirteenPlanes

noncomputable section

abbrev WeylMatrixSpace := Matrix (ZMod 3) (ZMod 3) ℂ

theorem weylMatrix_pairTrace (v w : WeylLabel) :
    Matrix.trace (weylMatrix (-v) * weylMatrix w) = if w=v then 3 else 0 := by
  rw [weylMatrix_mul, Matrix.trace_smul, weylMatrix_trace]
  by_cases h : w=v
  · subst w
    simp [symplecticBracket, mul_comm]
  · have hn : -v+w ≠ 0 := by intro hn; apply h; linear_combination hn
    simp [hn,h]

/-- Expansion of a matrix in the clock-and-shift basis. -/
def weylSynthesis : (WeylLabel → ℂ) →ₗ[ℂ] WeylMatrixSpace where
  toFun z := ∑ v, z v • weylMatrix v
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, smul_smul]

theorem weylSynthesis_coefficient (z : WeylLabel → ℂ) (v : WeylLabel) :
    Matrix.trace (weylMatrix (-v) * weylSynthesis z) = 3 * z v := by
  change Matrix.trace (weylMatrix (-v) * ∑ w, z w • weylMatrix w) = _
  rw [Finset.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul, weylMatrix_pairTrace, smul_eq_mul, mul_ite, mul_zero]
  simp [mul_comm]

theorem weylSynthesis_injective : Function.Injective weylSynthesis := by
  intro x y h
  funext v
  have eqn := congrArg (fun A => Matrix.trace (weylMatrix (-v) * A)) h
  change Matrix.trace (weylMatrix (-v) * weylSynthesis x) = Matrix.trace (weylMatrix (-v) * weylSynthesis y) at eqn
  rw [weylSynthesis_coefficient, weylSynthesis_coefficient] at eqn
  linear_combination eqn / 3

/-- All nine clock-and-shift coefficients parametrize the full matrix algebra. -/
def weylBasisEquiv : (WeylLabel → ℂ) ≃ₗ[ℂ] WeylMatrixSpace :=
  LinearEquiv.ofBijective weylSynthesis ⟨weylSynthesis_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      simp [WeylLabel, WeylMatrixSpace, Module.finrank_matrix])).mp weylSynthesis_injective⟩

end
end ThirteenPlanes
