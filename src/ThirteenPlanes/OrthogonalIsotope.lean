module

public import ThirteenPlanes.Isotope.Unitization
public import ThirteenPlanes.Isotope.NativeOctonion

@[expose] public section

set_option backward.privateInPublic true

/-! The three-slot isometry in the norm-composition isotope. -/

namespace ThirteenPlanes.MarkedPlane

open scoped Quaternion NativeOctonionEuclidean

variable {S₁ S₂ S₃ : Type*}
  [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁]
  [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂]
  [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃]

/-- Three onto real isometries intertwining a bilinear map with multiplication. -/
structure HurwitzIsotopy {K : Type*} [NormedAddCommGroup K] [Module ℝ K]
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (mul : K → K → K) where
  left : S₁ ≃ₗᵢ[ℝ] K
  right : S₂ ≃ₗᵢ[ℝ] K
  output : S₃ ≃ₗᵢ[ℝ] K
  map_mul : ∀ u y, output (φ u y) = mul (left u) (right y)

private theorem normForm_real (x : ℝ) : CompositionAlgebra.nf x = ‖x‖ ^ 2 := by
  rw [Real.nf_eq, Real.norm_eq_abs, sq_abs, pow_two]

private theorem normForm_complex (z : ℂ) : CompositionAlgebra.nf z = ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.nf_eq]

private theorem normForm_quaternion (q : Quaternion ℝ) : CompositionAlgebra.nf q = ‖q‖ ^ 2 := by
  change Quaternion.ipBilin q q = _
  rw [Quaternion.ipBilin_self, Quaternion.normSq_eq_norm_mul_self, pow_two]

private theorem OrthogonalProductUnitization.isotopyOfOutputEquiv
    {φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃} (U : OrthogonalProductUnitization φ)
    {K : Type*} [NormedAddCommGroup K] [Module ℝ K] {mul : K → K → K}
    (f : S₃ ≃ₗ[ℝ] K) (hnorm : ∀ p, ‖f p‖ ^ 2 = ‖p‖ ^ 2)
    (hmul : ∀ p q, f (U.product p q) = mul (f p) (f q)) :
    Nonempty (HurwitzIsotopy φ mul) := by
  let ρ : S₃ ≃ₗᵢ[ℝ] K :=
    ⟨f, fun p => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hnorm p)⟩
  refine ⟨⟨U.left.trans ρ, U.right.trans ρ, ρ, ?_⟩⟩
  intro u y
  change f (φ u y) = mul (f (U.left u)) (f (U.right y))
  rw [← U.product_apply, hmul]

variable [FiniteDimensional ℝ S₁] [FiniteDimensional ℝ S₂] [FiniteDimensional ℝ S₃]

/-- A norm-multiplicative product on three Euclidean slots is intertwined by
three onto isometries with multiplication on the Hurwitz algebra of their
common positive dimension. -/
/- Adolf Hurwitz's dimension restriction for norm-preserving bilinear maps is obtained here
by giving the output slot a unit and applying `CompositionAlgebra.hurwitz_classification`
from Bryan Ehrlich's composition-algebra formalization, as ported in Albert Sequential
Measurements. See Hurwitz (1898), pp. 309–316, and Baez, The Octonions, §1.1, Theorem 1. -/
theorem orthogonalProduct_isotopicToHurwitz
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃)
    (hφ : ∀ u y, ‖φ u y‖ = ‖u‖ * ‖y‖)
    {k : ℕ} (hk : 0 < k)
    (h₁ : Module.finrank ℝ S₁ = k) (h₂ : Module.finrank ℝ S₂ = k)
    (h₃ : Module.finrank ℝ S₃ = k) :
    (k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8) ∧
      ((k = 1 ∧ Nonempty (HurwitzIsotopy φ (fun x y : ℝ => x * y))) ∨
       (k = 2 ∧ Nonempty (HurwitzIsotopy φ (fun x y : ℂ => x * y))) ∨
       (k = 4 ∧ Nonempty (HurwitzIsotopy φ (fun x y : Quaternion ℝ => x * y))) ∨
       (k = 8 ∧ Nonempty (HurwitzIsotopy φ AlbertSequential.octonionMul))) := by
  obtain ⟨U⟩ := orthogonalProduct_hasUnitization φ hφ (h₁.trans h₃.symm)
    (h₂.trans h₃.symm) (h₃.symm ▸ hk)
  let := U.toNonAssocRing
  let := U.toIsScalarTower
  let := U.toSMulCommClass
  let := U.toCompositionAlgebra
  let : Nontrivial S₃ := Module.nontrivial_of_finrank_pos (h₃.symm ▸ hk)
  constructor
  · rw [← h₃]
    exact CompositionAlgebra.finrank_eq_one_or_two_or_four_or_eight (C := S₃)
  rcases CompositionAlgebra.hurwitz_classification (C := S₃) with
    ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩
  · refine Or.inl ⟨h₃.symm.trans (f.finrank_eq.trans Real.finrank_comp), ?_⟩
    exact U.isotopyOfOutputEquiv f
      (fun p => (normForm_real (f p)).symm.trans ((hf.map_nf p).trans (U.compositionNorm_eq p)))
      hf.map_mul
  · refine Or.inr (Or.inl ⟨h₃.symm.trans (f.finrank_eq.trans Complex.finrank_comp), ?_⟩)
    exact U.isotopyOfOutputEquiv f
      (fun p => (normForm_complex (f p)).symm.trans ((hf.map_nf p).trans (U.compositionNorm_eq p)))
      hf.map_mul
  · refine Or.inr (Or.inr (Or.inl ⟨h₃.symm.trans (f.finrank_eq.trans Quaternion.finrank_comp), ?_⟩))
    exact U.isotopyOfOutputEquiv f
      (fun p => (normForm_quaternion (f p)).symm.trans ((hf.map_nf p).trans (U.compositionNorm_eq p)))
      hf.map_mul
  · refine Or.inr (Or.inr (Or.inr ⟨h₃.symm.trans (f.finrank_eq.trans Octonion.finrank_comp), ?_⟩))
    refine U.isotopyOfOutputEquiv (f.trans hurwitzOctonionToNative) (fun p => ?_) (fun p q => ?_)
    · change ‖hurwitzOctonionToNative (f p)‖ ^ 2 = ‖p‖ ^ 2
      rw [hurwitzOctonionToNative_norm_sq, hf.map_nf, U.compositionNorm_eq]
    · change hurwitzOctonionToNative (f (p * q)) =
        AlbertSequential.octonionMul (hurwitzOctonionToNative (f p)) (hurwitzOctonionToNative (f q))
      rw [hf.map_mul, hurwitzOctonionToNative_mul]

end ThirteenPlanes.MarkedPlane
