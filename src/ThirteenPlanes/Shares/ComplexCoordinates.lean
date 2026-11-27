module

public import ThirteenPlanes.Shares.ThreePlanes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace

/-- The four complex monomials with zero or one conjugated argument. -/
def complexTriplePolynomial (a₀ a₁ a₂ a₃ x y z : ℂ) : ℂ :=
  a₀ * x * y * z + a₁ * star x * y * z + a₂ * x * star y * z + a₃ * x * y * star z

private theorem complexTriplePolynomial_sum_sq (a₀ a₁ a₂ a₃ : ℂ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      (complexTriplePolynomial a₀ a₁ a₂ a₃ (Complex.orthonormalBasisOneI i)
        (Complex.orthonormalBasisOneI j) (Complex.orthonormalBasisOneI k)).re ^ 2) =
      4 * (‖a₀‖ ^ 2 + ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 + ‖a₃‖ ^ 2) := by
  have h₀ : Complex.orthonormalBasisOneI 0 = 1 := by
    simp [Complex.coe_orthonormalBasisOneI]
  have h₁ : Complex.orthonormalBasisOneI 1 = Complex.I := by
    simp [Complex.coe_orthonormalBasisOneI]
  simp only [Fin.sum_univ_two, h₀, h₁, complexTriplePolynomial,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.star_def]
  norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {U U' W : Submodule ℝ V}

/-- The share equals the sum of squared moduli of the four normalized complex coefficients.
The mixed cubic on the three planes is six times the polarized form on their three inputs. -/
theorem shareOfThreePlanes_eq_sum_complex_coefficients (round : IsRound h 1)
    (orth : U.IsOrtho U') (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (zi : U ≃ₗᵢ[ℝ] ℂ) (zj : U' ≃ₗᵢ[ℝ] ℂ) (zk : W ≃ₗᵢ[ℝ] ℂ) (a₀ a₁ a₂ a₃ : ℂ)
    (coordinates : ∀ (x : U) (y : U') (z : W),
      6 * h.apply (x : V) (y : V) (z : V) =
        -3 * (complexTriplePolynomial a₀ a₁ a₂ a₃ (zi x) (zj y) (zk z)).re) :
    shareOfThreePlanes h U U' W = ‖a₀‖ ^ 2 + ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 + ‖a₃‖ ^ 2 := by
  let E := Complex.orthonormalBasisOneI.map zi.symm
  let F := Complex.orthonormalBasisOneI.map zj.symm
  let G := Complex.orthonormalBasisOneI.map zk.symm
  have dim : Module.finrank ℝ U = 2 := zi.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex
  rw [shareOfThreePlanes_eq_sum_cubic_sq round orth closed closed' dim E F G]
  have hsq (a b d : Fin 2) :
      (h.apply (E a : V) (F b : V) (G d : V)) ^ 2 =
        (1 / 4) * (complexTriplePolynomial a₀ a₁ a₂ a₃ (Complex.orthonormalBasisOneI a)
          (Complex.orthonormalBasisOneI b) (Complex.orthonormalBasisOneI d)).re ^ 2 := by
    have hc := coordinates (E a) (F b) (G d)
    simp only [E, F, G, OrthonormalBasis.map_apply, LinearIsometryEquiv.apply_symm_apply] at hc
    change 6 * h.apply (E a : V) (F b : V) (G d : V) = _ at hc
    have hh : h.apply (E a : V) (F b : V) (G d : V) =
        -(complexTriplePolynomial a₀ a₁ a₂ a₃ (Complex.orthonormalBasisOneI a)
          (Complex.orthonormalBasisOneI b) (Complex.orthonormalBasisOneI d)).re / 2 := by
      linarith only [hc]
    rw [hh]
    ring
  simp only [div_one, one_mul, hsq, ← Finset.mul_sum]
  rw [complexTriplePolynomial_sum_sq]
  ring

omit [FiniteDimensional ℝ V] in
/-- Inclusion-exclusion extracts the part of the cubic involving all three inputs. -/
theorem threeInputCubic_eq (g : SymmetricCubic V) (x y z : V) :
    g.apply (x + y + z) (x + y + z) (x + y + z) -
      g.apply (x + y) (x + y) (x + y) - g.apply (x + z) (x + z) (x + z) -
      g.apply (y + z) (y + z) (y + z) + g.apply x x x + g.apply y y y + g.apply z z z =
      6 * g.apply x y z := by
  have hyxz := g.apply_swap₁₂ y x z
  have hxzy := g.apply_swap₂₃ x z y
  have hzxy := (g.apply_swap₁₂ z x y).trans hxzy
  have hyzx := (g.apply_swap₂₃ y z x).trans hyxz
  have hzyx := (g.apply_swap₁₂ z y x).trans hyzx
  simp only [SymmetricCubic.apply_add₁, SymmetricCubic.apply_add₂, SymmetricCubic.apply_add₃,
    hyxz, hxzy, hzxy, hyzx, hzyx]
  ring

end ThirteenPlanes.RoundCubics
