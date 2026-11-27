module

public import ThirteenPlanes.Peirce.SlotCubic
public import ThirteenPlanes.FourPlanes
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

set_option backward.privateInPublic true

/-! Explicit marked coordinates for the complex Hermitian three-by-three model. -/

open scoped Matrix BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open SymmetricCubic

/-- The actual Hermitian matrix with real diagonal and entries at positions 23, 13, 12. -/
def complexSlotMatrix (a b d : ℝ) (p q r : ℂ) : ComplexMatrix3 :=
  !![(a : ℂ), r, q; star r, (b : ℂ), p; star q, star p, (d : ℂ)]

theorem complexSlotMatrix_isHermitian (a b d : ℝ) (p q r : ℂ) :
    (complexSlotMatrix a b d p q r).IsHermitian := by
  change (complexSlotMatrix a b d p q r)ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexSlotMatrix, Matrix.conjTranspose_apply]

theorem complexSlotMatrix_trace (a b d : ℝ) (p q r : ℂ) :
    Matrix.trace (complexSlotMatrix a b d p q r) = ((a + b + d : ℝ) : ℂ) := by
  simp [Matrix.trace, Fin.sum_univ_three, complexSlotMatrix]

/-- The trace pairing in raw diagonal and off-diagonal coordinates. -/
theorem complexSlotMatrix_tracePairing (a b d a' b' d' : ℝ)
    (p q r p' q' r' : ℂ) :
    tracePairing (complexSlotMatrix a b d p q r) (complexSlotMatrix a' b' d' p' q' r') =
      a * a' + b * b' + d * d' + 2 * (⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫) := by
  simp [tracePairing, Matrix.trace, Fin.sum_univ_three, complexSlotMatrix,
    Complex.inner, Complex.mul_re]
  ring

/-- The raw real trace of the actual matrix cube. -/
theorem complexSlotMatrix_trace_cube (a b d : ℝ) (p q r : ℂ) :
    (Matrix.trace ((complexSlotMatrix a b d p q r) ^ 3)).re =
      a ^ 3 + b ^ 3 + d ^ 3 +
      3 * (b + d) * ‖p‖ ^ 2 + 3 * (a + d) * ‖q‖ ^ 2 + 3 * (a + b) * ‖r‖ ^ 2 +
      6 * ⟪q * star p, r⟫ := by
  rw [← Complex.normSq_eq_norm_sq p, ← Complex.normSq_eq_norm_sq q, ← Complex.normSq_eq_norm_sq r]
  simp [pow_succ, pow_zero, one_mul, Matrix.trace, Fin.sum_univ_three,
    complexSlotMatrix, Complex.inner, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring


private abbrev s₂ : ℝ := (Real.sqrt 2)⁻¹
private abbrev s₆ : ℝ := (Real.sqrt 6)⁻¹

private theorem s₂_sq : s₂ ^ 2 = 1 / 2 := by
  unfold s₂
  rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num

private theorem s₆_sq : s₆ ^ 2 = 1 / 6 := by
  unfold s₆
  rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ))]
  norm_num

private theorem sqrt_s₆ : Real.sqrt 6 * s₆ = 1 :=
  mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num)).ne'

private theorem sqrt_s₂ : Real.sqrt 6 * s₂ = Real.sqrt 3 := by
  unfold s₂
  rw [show (6 : ℝ) = 3 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
    mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', mul_one]

/-- The actual normalized marked Hermitian matrix, using the manuscript's entry positions. -/
def complexCartanMatrix (α β : ℝ) (p q r : ℂ) : ComplexMatrix3 :=
  complexSlotMatrix (2 * (s₆ * α)) (-(s₆ * α) + s₂ * β) (-(s₆ * α) - s₂ * β)
    (s₂ • p) (s₂ • q) (s₂ • r)

/-- The normalized marked coordinates valued in the actual traceless Hermitian carrier. -/
def complexCartanField (α β : ℝ) (p q r : ℂ) : TracelessHermitian3 :=
  TracelessHermitian3.ofMatrix (complexCartanMatrix α β p q r)
    (complexSlotMatrix_isHermitian _ _ _ _ _ _) (by
      unfold complexCartanMatrix
      rw [complexSlotMatrix_trace]
      norm_cast
      ring)

@[simp] theorem toMatrix_complexCartanField (α β : ℝ) (p q r : ℂ) :
    TracelessHermitian3.toMatrix (complexCartanField α β p q r) =
      complexCartanMatrix α β p q r := rfl

/-- The normalized matrix coordinates have the direct-sum inner product in the actual trace metric. -/
theorem complexCartanField_inner (α β α' β' : ℝ) (p q r p' q' r' : ℂ) :
    ⟪complexCartanField α β p q r, complexCartanField α' β' p' q' r'⟫ =
      α * α' + β * β' + ⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫ := by
  rw [TracelessHermitian3.inner_eq_tracePairing, toMatrix_complexCartanField,
    toMatrix_complexCartanField, complexCartanMatrix, complexCartanMatrix,
    complexSlotMatrix_tracePairing]
  simp only [real_inner_smul_left, real_inner_smul_right]
  calc
    _ = (6 * s₆ ^ 2) * (α * α') + (2 * s₂ ^ 2) *
        (β * β' + ⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫) := by ring
    _ = _ := by rw [s₂_sq, s₆_sq]; ring

/-- The five coordinates map real-linearly into the actual Hermitian carrier. -/
def complexCartanLinear : (ℝ × ℝ × ℂ × ℂ × ℂ) →ₗ[ℝ] TracelessHermitian3 where
  toFun t := complexCartanField t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  map_add' t w := by
    rcases t with ⟨α, β, p, q, r⟩
    rcases w with ⟨α', β', p', q', r'⟩
    apply TracelessHermitian3.toMatrix_injective
    simp only [map_add, Prod.fst_add, Prod.snd_add, toMatrix_complexCartanField]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [complexCartanMatrix, complexSlotMatrix, Complex.real_smul, star_add] <;> ring
  map_smul' c t := by
    rcases t with ⟨α, β, p, q, r⟩
    apply TracelessHermitian3.toMatrix_injective
    simp only [RingHom.id_apply, map_smul,
      toMatrix_complexCartanField]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [complexCartanMatrix, complexSlotMatrix, Complex.real_smul, star_mul, smul_eq_mul] <;> ring

theorem complexCartanField_norm_sq (α β : ℝ) (p q r : ℂ) :
    ‖complexCartanField α β p q r‖ ^ 2 = α ^ 2 + β ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, complexCartanField_inner]
  simp only [real_inner_self_eq_norm_sq, pow_two]

private theorem complexCartanLinear_bijective : Function.Bijective complexCartanLinear := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨α, β, p, q, r⟩ hx
    change complexCartanField α β p q r = 0 at hx
    have h := complexCartanField_norm_sq α β p q r
    rw [hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    have hα : α = 0 := by nlinarith only [h, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
    have hβ : β = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg ‖p‖, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
    have hp : ‖p‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
    have hq : ‖q‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖r‖]
    have hr : ‖r‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖q‖]
    rw [hα, hβ, norm_eq_zero.mp hp, norm_eq_zero.mp hq, norm_eq_zero.mp hr]
    rfl
  · intro x
    let m := TracelessHermitian3.toMatrix x
    let d₀ := (m 0 0).re
    let d₁ := (m 1 1).re
    have h₂ : s₂ * Real.sqrt 2 = 1 :=
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have h₆ : s₆ * Real.sqrt 6 = 1 := by rw [mul_comm, sqrt_s₆]
    let α := Real.sqrt 6 * (d₀ / 2)
    let β := Real.sqrt 2 * (d₁ + d₀ / 2)
    have hα : s₆ * α = d₀ / 2 := by rw [show α = Real.sqrt 6 * (d₀ / 2) from rfl, ← mul_assoc, h₆, one_mul]
    have hβ : s₂ * β = d₁ + d₀ / 2 := by
      rw [show β = Real.sqrt 2 * (d₁ + d₀ / 2) from rfl, ← mul_assoc, h₂, one_mul]
    refine ⟨(α, β, Real.sqrt 2 • m 1 2, Real.sqrt 2 • m 0 2, Real.sqrt 2 • m 0 1), ?_⟩
    apply TracelessHermitian3.independentEntries_injective
    change TracelessHermitian3.independentEntries (complexCartanField α β _ _ _) = _
    apply Prod.ext
    · funext i
      fin_cases i
      all_goals simp [TracelessHermitian3.independentEntries, complexCartanMatrix, complexSlotMatrix,
        hα, hβ, d₀, d₁, m]
      ring
    · funext i
      fin_cases i <;>
        simp [TracelessHermitian3.independentEntries, complexCartanMatrix, complexSlotMatrix,
          m]

/-- Existence and uniqueness of the normalized coordinates in the actual complex trace carrier. -/
def complexCartanEquiv : (ℝ × ℝ × ℂ × ℂ × ℂ) ≃ₗ[ℝ] TracelessHermitian3 :=
  LinearEquiv.ofBijective complexCartanLinear complexCartanLinear_bijective

@[simp] theorem complexCartanEquiv_apply (α β : ℝ) (p q r : ℂ) :
    complexCartanEquiv (α, β, p, q, r) = complexCartanField α β p q r := rfl

/-- The normalized cubic of the actual complex trace-free Hermitian model. -/
def complexCartanCubic : SymmetricCubic TracelessHermitian3 :=
  Real.sqrt 6 • matrixEqualCubic

/-- The whole cubic is the polarized trace on the actual complex Hermitian matrices. -/
theorem complexCartanCubic_apply (x y z : TracelessHermitian3) :
    complexCartanCubic.apply x y z =
      Real.sqrt 6 * tracePairing (symmetricMatrixProduct (TracelessHermitian3.toMatrix x)
        (TracelessHermitian3.toMatrix y)) (TracelessHermitian3.toMatrix z) := by
  rw [complexCartanCubic, apply_smul]
  change Real.sqrt 6 * ⟪TracelessHermitian3.jordan x y, z⟫ = _
  rw [TracelessHermitian3.inner_eq_tracePairing, TracelessHermitian3.toMatrix_jordan,
    tracePairing_traceFreePart_left _ _ z.trace_eq_zero]

/-- Its diagonal polynomial is `√6 Re tr(X³)` on the actual traceless matrices. -/
theorem complexCartanCubic_diagonal (x : TracelessHermitian3) :
    complexCartanCubic.apply x x x =
      Real.sqrt 6 * (Matrix.trace ((TracelessHermitian3.toMatrix x) ^ 3)).re := by
  rw [complexCartanCubic, apply_smul]
  change Real.sqrt 6 * ⟪TracelessHermitian3.jordan x x, x⟫ = _
  rw [TracelessHermitian3.jordan_self, TracelessHermitian3.inner_eq_tracePairing,
    TracelessHermitian3.toMatrix_square, tracelessSquare,
    tracePairing_traceFreePart_left _ _ x.trace_eq_zero, tracePairing, pow_succ, pow_two]

private theorem s₂_smul_norm_sq (z : ℂ) : ‖s₂ • z‖ ^ 2 = s₂ ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem s₂_triple_inner (p q r : ℂ) :
    ⟪(s₂ • q) * star (s₂ • p), s₂ • r⟫ = s₂ ^ 3 * ⟪q * star p, r⟫ := by
  rw [star_smul, star_trivial, smul_mul_smul_comm, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The full normalized Cartan polynomial in the marked complex trace coordinates. -/
theorem complexCartanCubic_normalForm (α β : ℝ) (p q r : ℂ) :
    let x := complexCartanField α β p q r
    complexCartanCubic.apply x x x =
      α ^ 3 - 3 * α * (β ^ 2 + ‖p‖ ^ 2) +
      (3 / 2 : ℝ) * α * (‖q‖ ^ 2 + ‖r‖ ^ 2) +
      (3 * Real.sqrt 3 / 2) * β * (‖r‖ ^ 2 - ‖q‖ ^ 2) +
      3 * Real.sqrt 3 * ⟪q * star p, r⟫ := by
  dsimp only
  rw [complexCartanCubic_diagonal, toMatrix_complexCartanField, complexCartanMatrix,
    complexSlotMatrix_trace_cube, s₂_smul_norm_sq, s₂_smul_norm_sq, s₂_smul_norm_sq, s₂_triple_inner]
  calc
    _ = (Real.sqrt 6 * s₆) *
        (6 * s₆ ^ 2 * α ^ 3 - 6 * s₂ ^ 2 * α * (β ^ 2 + ‖p‖ ^ 2) +
          3 * s₂ ^ 2 * α * (‖q‖ ^ 2 + ‖r‖ ^ 2)) +
        (Real.sqrt 6 * s₂) * (3 * s₂ ^ 2 * β * (‖r‖ ^ 2 - ‖q‖ ^ 2) +
          6 * s₂ ^ 2 * ⟪q * star p, r⟫) := by ring
    _ = _ := by rw [sqrt_s₆, sqrt_s₂, s₂_sq, s₆_sq]; ring


end

end ThirteenPlanes.Peirce
