module

public import ThirteenPlanes.Peirce.SlotComplexModel

@[expose] public section

set_option backward.privateInPublic true

/-! The actual real symmetric trace-zero model with its trace metric. -/

open scoped Matrix BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

abbrev RealMatrix3 := Matrix (Fin 3) (Fin 3) ℝ

private def realCartanCoordinates : (ℝ × ℝ × ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℂ × ℂ × ℂ) where
  toFun x := (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2)
  map_add' x y := by
    rcases x with ⟨a, b, p, q, r⟩
    rcases y with ⟨a', b', p', q', r'⟩
    simp [Complex.ofReal_add]
  map_smul' c x := by
    rcases x with ⟨a, b, p, q, r⟩
    simp [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]

private theorem realCartanCoordinates_injective : Function.Injective realCartanCoordinates := by
  rintro ⟨a, b, p, q, r⟩ ⟨a', b', p', q', r'⟩ h
  change ((a,b,(p : ℂ),(q : ℂ),(r : ℂ)) : ℝ × ℝ × ℂ × ℂ × ℂ) = (a', b', (p' : ℂ), (q' : ℂ), (r' : ℂ)) at h
  simpa only [Prod.mk.injEq, Complex.ofReal_inj] using h

private def realCartanLinear : (ℝ × ℝ × ℝ × ℝ × ℝ) →ₗ[ℝ] TracelessHermitian3 :=
  complexCartanEquiv.toLinearMap.comp realCartanCoordinates

/-- The actual real symmetric traceless matrices realized as the real-entry subspace of the
complex Hermitian trace Hilbert space. -/
def realTraceSubmodule : Submodule ℝ TracelessHermitian3 := realCartanLinear.range

abbrev RealTracelessSymmetric3 := realTraceSubmodule

instance : InnerProductSpace ℝ RealTracelessSymmetric3 :=
  Submodule.innerProductSpace (𝕜 := ℝ) (E := TracelessHermitian3) realTraceSubmodule

/-- Five normalized real coordinates parametrizing the whole real trace carrier. -/
def realCartanEquiv : (ℝ × ℝ × ℝ × ℝ × ℝ) ≃ₗ[ℝ] RealTracelessSymmetric3 :=
  LinearEquiv.ofInjective realCartanLinear (complexCartanEquiv.injective.comp realCartanCoordinates_injective)

instance : FiniteDimensional ℝ RealTracelessSymmetric3 := realCartanEquiv.finiteDimensional

/-- The literal real symmetric matrix of an element. -/
def realTraceMatrix (x : RealTracelessSymmetric3) : RealMatrix3 :=
  fun i j => (TracelessHermitian3.toMatrix x.1 i j).re

private abbrev s₂ : ℝ := (Real.sqrt 2)⁻¹
private abbrev s₆ : ℝ := (Real.sqrt 6)⁻¹

/-- The coordinate matrix in the real Hermitian model. -/
theorem realTraceMatrix_coordinates (α β p q r : ℝ) :
    realTraceMatrix (realCartanEquiv (α, β, p, q, r)) =
      !![2 * (s₆ * α), s₂ * r, s₂ * q;
        s₂ * r, -(s₆ * α) + s₂ * β, s₂ * p;
        s₂ * q, s₂ * p, -(s₆ * α) - s₂ * β] := by
  have h₂ : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h₆ : Real.sqrt 6 / 6 = (Real.sqrt 6)⁻¹ := by
    have hpos : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  ext i j
  change (complexCartanMatrix α β p q r i j).re = _
  fin_cases i <;> fin_cases j <;>
    simp [complexCartanMatrix, complexSlotMatrix, Complex.real_smul, s₂, s₆, h₂, h₆]

/-- The carrier's literal matrices are exactly the symmetric real matrices of trace zero. -/
theorem realTraceMatrix_range (A : RealMatrix3) :
    (∃ x : RealTracelessSymmetric3, realTraceMatrix x = A) ↔ Aᵀ = A ∧ Matrix.trace A = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨α, β, p, q, r⟩, rfl⟩ := realCartanEquiv.surjective x
    rw [realTraceMatrix_coordinates]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · simp [Matrix.trace, Fin.sum_univ_three]
      ring
  · rintro ⟨hA, ht⟩
    have h₂ : s₂ * Real.sqrt 2 = 1 :=
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have h₆ : s₆ * Real.sqrt 6 = 1 :=
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne'
    have hdiag : A 0 0 + A 1 1 + A 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using ht
    let α := Real.sqrt 6 * (A 0 0 / 2)
    let β := Real.sqrt 2 * (A 1 1 + A 0 0 / 2)
    have hα : s₆ * α = A 0 0 / 2 := by
      rw [show α = Real.sqrt 6 * (A 0 0 / 2) from rfl, ← mul_assoc, h₆, one_mul]
    have hβ : s₂ * β = A 1 1 + A 0 0 / 2 := by
      rw [show β = Real.sqrt 2 * (A 1 1 + A 0 0 / 2) from rfl, ← mul_assoc, h₂, one_mul]
    have hsym (i j : Fin 3) : A j i = A i j := congrFun (congrFun hA i) j
    refine ⟨realCartanEquiv (α, β, Real.sqrt 2 * A 1 2, Real.sqrt 2 * A 0 2,
      Real.sqrt 2 * A 0 1), ?_⟩
    rw [realTraceMatrix_coordinates]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hα, hβ]
    all_goals first | linarith only [hdiag] | exact hsym _ _

private def realTraceInclusion : RealTracelessSymmetric3 →ₗ[ℝ] TracelessHermitian3 :=
  realTraceSubmodule.subtype

private theorem complexMatrix_realTrace (x : RealTracelessSymmetric3) :
    TracelessHermitian3.toMatrix x.1 = (realTraceMatrix x).map Complex.ofReal := by
  obtain ⟨⟨α, β, p, q, r⟩, rfl⟩ := realCartanEquiv.surjective x
  rw [realTraceMatrix_coordinates]
  ext i j
  change complexCartanMatrix α β p q r i j = _
  fin_cases i <;> fin_cases j <;>
    simp [complexCartanMatrix, complexSlotMatrix, Complex.real_smul]

/-- The actual trace form on the real matrices. -/
theorem realTraceMatrix_inner (x y : RealTracelessSymmetric3) :
    ⟪x, y⟫ = Matrix.trace (realTraceMatrix x * realTraceMatrix y) := by
  change ⟪x.1, y.1⟫ = _
  rw [TracelessHermitian3.inner_eq_tracePairing, complexMatrix_realTrace, complexMatrix_realTrace]
  simp [tracePairing, Matrix.trace, Matrix.mul_apply]

/-- The normalized cubic restricted to the real symmetric trace carrier. -/
def realCartanCubic : SymmetricCubic RealTracelessSymmetric3 :=
  complexCartanCubic.pullback realTraceInclusion

/-- The normalized polynomial is the real matrix trace of the cube. -/
theorem realCartanCubic_diagonal (x : RealTracelessSymmetric3) :
    realCartanCubic.apply x x x = Real.sqrt 6 * Matrix.trace ((realTraceMatrix x) ^ 3) := by
  rw [realCartanCubic, SymmetricCubic.pullback_apply]
  change complexCartanCubic.apply x.1 x.1 x.1 = _
  rw [complexCartanCubic_diagonal, complexMatrix_realTrace]
  simp [pow_succ, pow_zero, Matrix.trace, Matrix.mul_apply]

theorem realCartanField_norm_sq (α β p q r : ℝ) :
    ‖realCartanEquiv (α, β, p, q, r)‖ ^ 2 = α ^ 2 + β ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2 := by
  change ‖complexCartanField α β (p : ℂ) (q : ℂ) (r : ℂ)‖ ^ 2 = _
  simpa [Complex.norm_real] using complexCartanField_norm_sq α β p q r

set_option maxHeartbeats 1200000 in
/-- The complete normalized Cartan polynomial on the actual real matrix carrier. -/
theorem realCartanCubic_normalForm (α β p q r : ℝ) :
    let x := realCartanEquiv (α, β, p, q, r)
    realCartanCubic.apply x x x =
      α ^ 3 - 3 * α * (β ^ 2 + ‖p‖ ^ 2) +
      (3 / 2 : ℝ) * α * (‖q‖ ^ 2 + ‖r‖ ^ 2) +
      (3 * Real.sqrt 3 / 2) * β * (‖r‖ ^ 2 - ‖q‖ ^ 2) +
      3 * Real.sqrt 3 * ⟪q * p, r⟫ := by
  dsimp only
  rw [realCartanCubic, SymmetricCubic.pullback_apply]
  change complexCartanCubic.apply (complexCartanField α β p q r)
    (complexCartanField α β p q r) (complexCartanField α β p q r) = _
  simpa [Complex.inner, Complex.norm_real, Complex.mul_re, Real.inner_apply, mul_comm] using
    complexCartanCubic_normalForm α β p q r

end

end ThirteenPlanes.Peirce
