module

public import ThirteenPlanes.Quaternionic.NativeTraceModel
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

set_option backward.privateInPublic true

/-! The marked trace coordinates and cubic of the actual quaternionic Hermitian model. -/

open scoped Quaternion Matrix BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open QuaternionicMUB SymmetricCubic

/-- The native quaternionic Hermitian matrix in raw diagonal and slot coordinates. -/
def quaternionSlotMatrix (a b d : ℝ) (p q r : Q) : QMat :=
  matrixOfHermCoordinates ![a,b,d] ![r,q,p]

theorem quaternionSlotMatrix_trace (a b d : ℝ) (p q r : Q) :
    rtrace (quaternionSlotMatrix a b d p q r) = a + b + d := by
  simp [rtrace, Fin.sum_univ_three, quaternionSlotMatrix, matrixOfHermCoordinates]

private theorem quaternionMatrix_mul_entry (A B : QMat) (i j : Outcome) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]

/-- The trace pairing of the actual native quaternionic matrices. -/
theorem quaternionSlotMatrix_tracePairing (a b d a' b' d' : ℝ)
    (p q r p' q' r' : Q) :
    traceForm (quaternionSlotMatrix a b d p q r) (quaternionSlotMatrix a' b' d' p' q' r') =
      a * a' + b * b' + d * d' + 2 * (⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫) := by
  rw [traceForm_eq_rtrace_mul]
  simp only [rtrace, Fin.sum_univ_three, quaternionMatrix_mul_entry]
  simp [quaternionSlotMatrix, matrixOfHermCoordinates, Quaternion.inner_def]
  ring

/-- The raw real trace of the cube on the actual quaternionic matrix carrier. -/
theorem quaternionSlotMatrix_trace_cube (a b d : ℝ) (p q r : Q) :
    rtrace ((quaternionSlotMatrix a b d p q r) ^ 3) =
      a ^ 3 + b ^ 3 + d ^ 3 +
      3 * (b + d) * ‖p‖ ^ 2 + 3 * (a + d) * ‖q‖ ^ 2 + 3 * (a + b) * ‖r‖ ^ 2 +
      6 * ⟪q * star p, r⟫ := by
  have hn (x : Q) : ‖x‖ ^ 2 = Quaternion.normSq x := by
    rw [pow_two, Quaternion.normSq_eq_norm_mul_self]
  rw [hn p, hn q, hn r, pow_succ, pow_two]
  simp only [rtrace, Fin.sum_univ_three, quaternionMatrix_mul_entry]
  simp [quaternionSlotMatrix, matrixOfHermCoordinates, Quaternion.inner_def, Quaternion.normSq_def']
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

/-- The normalized marked coordinates in the actual quaternionic matrix carrier. -/
def quaternionCartanMatrix (α β : ℝ) (p q r : Q) : QMat :=
  quaternionSlotMatrix (2 * (s₆ * α)) (-(s₆ * α) + s₂ * β) (-(s₆ * α) - s₂ * β)
    (s₂ • p) (s₂ • q) (s₂ • r)

def quaternionCartanField (α β : ℝ) (p q r : Q) : TracelessHilbert :=
  traceOfMatrix (quaternionCartanMatrix α β p q r)
    (matrixOfHermCoordinates_isHermitian _ _) (by
      unfold quaternionCartanMatrix
      rw [quaternionSlotMatrix_trace]
      ring)

@[simp] theorem traceMat_quaternionCartanField (α β : ℝ) (p q r : Q) :
    traceMat (quaternionCartanField α β p q r) = quaternionCartanMatrix α β p q r :=
  traceMat_ofMatrix _ _ _

/-- The normalized coordinates have the direct-sum metric in the actual trace geometry. -/
theorem quaternionCartanField_inner (α β α' β' : ℝ) (p q r p' q' r' : Q) :
    ⟪quaternionCartanField α β p q r, quaternionCartanField α' β' p' q' r'⟫ =
      α * α' + β * β' + ⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫ := by
  rw [tracelessHilbert_inner]
  change traceForm (traceMat (quaternionCartanField α β p q r))
    (traceMat (quaternionCartanField α' β' p' q' r')) = _
  rw [traceMat_quaternionCartanField, traceMat_quaternionCartanField,
    quaternionCartanMatrix, quaternionCartanMatrix, quaternionSlotMatrix_tracePairing]
  simp only [real_inner_smul_left, real_inner_smul_right]
  calc
    _ = (6 * s₆ ^ 2) * (α * α') + (2 * s₂ ^ 2) *
        (β * β' + ⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫) := by ring
    _ = _ := by rw [s₂_sq, s₆_sq]; ring

theorem quaternionCartanField_norm_sq (α β : ℝ) (p q r : Q) :
    ‖quaternionCartanField α β p q r‖ ^ 2 = α ^ 2 + β ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, quaternionCartanField_inner]
  simp only [real_inner_self_eq_norm_sq, pow_two]

/-- The normalized coordinates map real-linearly into the native trace carrier. -/
def quaternionCartanLinear : (ℝ × ℝ × Q × Q × Q) →ₗ[ℝ] TracelessHilbert where
  toFun t := quaternionCartanField t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  map_add' t w := by
    rcases t with ⟨α, β, p, q, r⟩
    rcases w with ⟨α', β', p', q', r'⟩
    apply traceMat_injective
    simp only [map_add, Prod.fst_add, Prod.snd_add, traceMat_quaternionCartanField]
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      simp [quaternionCartanMatrix, quaternionSlotMatrix, matrixOfHermCoordinates, smul_add,
        star_add, ← Quaternion.coe_add]
    all_goals first | (apply Quaternion.ext <;> simp <;> ring) | ring
  map_smul' c t := by
    rcases t with ⟨α, β, p, q, r⟩
    apply traceMat_injective
    simp only [RingHom.id_apply, map_smul, traceMat_quaternionCartanField]
    apply Matrix.ext
    intro i j
    change quaternionCartanMatrix (c * α) (c * β) (c • p) (c • q) (c • r) i j =
      c • quaternionCartanMatrix α β p q r i j
    fin_cases i <;> fin_cases j <;>
      simp [quaternionCartanMatrix, quaternionSlotMatrix, matrixOfHermCoordinates, star_smul,
        smul_smul, mul_comm]
    all_goals apply Quaternion.ext <;> simp <;> ring

private theorem quaternionCartanLinear_injective : Function.Injective quaternionCartanLinear := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  rintro ⟨α, β, p, q, r⟩ hx
  change quaternionCartanField α β p q r = 0 at hx
  have h := quaternionCartanField_norm_sq α β p q r
  rw [hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  have hα : α = 0 := by nlinarith only [h, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
  have hβ : β = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg ‖p‖, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
  have hp : ‖p‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
  have hq : ‖q‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖r‖]
  have hr : ‖r‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖q‖]
  rw [hα, hβ, norm_eq_zero.mp hp, norm_eq_zero.mp hq, norm_eq_zero.mp hr]
  rfl

/-- The normalized coordinates are onto the actual quaternionic traceless Hermitian space. -/
def quaternionCartanEquiv : (ℝ × ℝ × Q × Q × Q) ≃ₗ[ℝ] TracelessHilbert :=
  quaternionCartanLinear.linearEquivOfInjective quaternionCartanLinear_injective (by
    rw [finrank_TracelessHilbert]
    norm_num [Module.finrank_prod, Quaternion.finrank_eq_four])

@[simp] theorem quaternionCartanEquiv_apply (α β : ℝ) (p q r : Q) :
    quaternionCartanEquiv (α, β, p, q, r) = quaternionCartanField α β p q r := rfl

/-- The actual quaternionic trace cubic, normalized to round strength one. -/
def quaternionCartanCubic : SymmetricCubic TracelessHilbert := Real.sqrt 6 • quaternionTraceCubic

theorem quaternionCartanCubic_apply (x y z : TracelessHilbert) :
    quaternionCartanCubic.apply x y z =
      Real.sqrt 6 * rtrace (jordan (jordan (traceMat x) (traceMat y)) (traceMat z)) := by
  rw [quaternionCartanCubic, apply_smul, quaternionTraceCubic_apply, quaternionFullCubic_apply]
  simp only [fullMat_traceInclusion]

theorem quaternionCartanCubic_diagonal (x : TracelessHilbert) :
    quaternionCartanCubic.apply x x x = Real.sqrt 6 * rtrace ((traceMat x) ^ 3) := by
  rw [quaternionCartanCubic_apply, jordan_self, ← traceForm, traceForm_eq_rtrace_mul, pow_succ, pow_two]

private theorem s₂_smul_norm_sq (z : Q) : ‖s₂ • z‖ ^ 2 = s₂ ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem s₂_triple_inner (p q r : Q) :
    ⟪(s₂ • q) * star (s₂ • p), s₂ • r⟫ = s₂ ^ 3 * ⟪q * star p, r⟫ := by
  rw [star_smul, star_trivial, smul_mul_smul_comm, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The full normalized Cartan polynomial in the marked quaternion trace coordinates. -/
theorem quaternionCartanCubic_normalForm (α β : ℝ) (p q r : Q) :
    let x := quaternionCartanField α β p q r
    quaternionCartanCubic.apply x x x =
      α ^ 3 - 3 * α * (β ^ 2 + ‖p‖ ^ 2) +
      (3 / 2 : ℝ) * α * (‖q‖ ^ 2 + ‖r‖ ^ 2) +
      (3 * Real.sqrt 3 / 2) * β * (‖r‖ ^ 2 - ‖q‖ ^ 2) +
      3 * Real.sqrt 3 * ⟪q * star p, r⟫ := by
  dsimp only
  rw [quaternionCartanCubic_diagonal, traceMat_quaternionCartanField, quaternionCartanMatrix,
    quaternionSlotMatrix_trace_cube, s₂_smul_norm_sq, s₂_smul_norm_sq, s₂_smul_norm_sq, s₂_triple_inner]
  calc
    _ = (Real.sqrt 6 * s₆) *
        (6 * s₆ ^ 2 * α ^ 3 - 6 * s₂ ^ 2 * α * (β ^ 2 + ‖p‖ ^ 2) +
          3 * s₂ ^ 2 * α * (‖q‖ ^ 2 + ‖r‖ ^ 2)) +
        (Real.sqrt 6 * s₂) * (3 * s₂ ^ 2 * β * (‖r‖ ^ 2 - ‖q‖ ^ 2) +
          6 * s₂ ^ 2 * ⟪q * star p, r⟫) := by ring
    _ = _ := by rw [sqrt_s₆, sqrt_s₂, s₂_sq, s₆_sq]; ring


end

end ThirteenPlanes.Peirce
