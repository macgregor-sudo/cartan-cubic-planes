module

public import ThirteenPlanes.Cartan.Casimir
public import ThirteenPlanes.Quaternionic.ImaginaryConjugation
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-! The real rotation blocks of the diagonal Cartan actions. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped BigOperators Matrix RealInnerProductSpace

noncomputable section

/-- The literal action (x mapsto a i x - x b i) on one quaternionic entry. -/
def quaternionWeight (a b : ℝ) : Module.End ℝ Q where
  toFun x := (a • qi) * x - x * (b • qi)
  map_add' x y := by simp only [mul_add, add_mul]; abel
  map_smul' r x := by
    change _ * (r • x) - (r • x) * _ = r • (_ * x - x * _)
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub, smul_comm b r]

theorem quaternionWeight_apply (a b : ℝ) (x : Q) :
    quaternionWeight a b x =
      ⟨-(a - b) * x.imI, (a - b) * x.re, -(a + b) * x.imK, (a + b) * x.imJ⟩ := by
  change (a • qi) * x - x * (b • qi) = _
  apply Quaternion.ext <;>
    simp [qi] <;>
    ring

/-- The two real rotation planes in a quaternionic slot have speeds (a-b) and (a+b). -/
theorem quaternionWeight_comp_apply (a b c d : ℝ) (x : Q) :
    (quaternionWeight a b * quaternionWeight c d) x =
      ⟨-((a - b) * (c - d)) * x.re, -((a - b) * (c - d)) * x.imI,
        -((a + b) * (c + d)) * x.imJ, -((a + b) * (c + d)) * x.imK⟩ := by
  rw [mul_apply_eq_comp, quaternionWeight_apply a b, quaternionWeight_apply c d]
  apply Quaternion.ext <;> simp <;> ring

theorem quaternionWeight_trace_mul (a b c d : ℝ) :
    LinearMap.trace ℝ Q (quaternionWeight a b * quaternionWeight c d) =
      -4 * (a * c + b * d) := by
  let B : Module.Basis (Fin 4) ℝ Q := QuaternionAlgebra.basisOneIJK (-1) 0 (-1)
  rw [LinearMap.trace_eq_matrix_trace ℝ B, Matrix.trace, Fin.sum_univ_four]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, quaternionWeight_comp_apply]
  have h (i : Fin 4) : B.repr (B i) i = 1 := by simp
  have h0 : (B 0).re = 1 := h 0
  have h1 : (B 1).imI = 1 := h 1
  have h2 : (B 2).imJ = 1 := h 2
  have h3 : (B 3).imK = 1 := h 3
  change -((a - b) * (c - d)) * (B 0).re + -((a - b) * (c - d)) * (B 1).imI +
      -((a + b) * (c + d)) * (B 2).imJ + -((a + b) * (c + d)) * (B 3).imK = _
  rw [h0, h1, h2, h3]
  ring

theorem quaternionWeight_left_right_sq (x : Q) :
    quaternionWeight 1 0 (quaternionWeight 1 0 x) = -x ∧
      quaternionWeight 0 1 (quaternionWeight 0 1 x) = -x := by
  constructor <;>
    rw [← mul_apply_eq_comp, quaternionWeight_comp_apply] <;>
    apply Quaternion.ext <;> norm_num

/-- The action on a complex entry at weight (a-b). -/
def complexWeight (a b : ℝ) : Module.End ℝ ℂ where
  toFun x := ((a - b : ℝ) : ℂ) * Complex.I * x
  map_add' _ _ := mul_add _ _ _
  map_smul' r x := by simp [Complex.real_smul]; ring

theorem complexWeight_apply (a b : ℝ) (x : ℂ) :
    complexWeight a b x = ⟨-(a - b) * x.im, (a - b) * x.re⟩ := by
  change ((a - b : ℝ) : ℂ) * Complex.I * x = _
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_sub]
    ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_sub]

theorem complexWeight_comp_apply (a b c d : ℝ) (x : ℂ) :
    (complexWeight a b * complexWeight c d) x = (-((a - b) * (c - d))) • x := by
  rw [mul_apply_eq_comp, complexWeight_apply a b, complexWeight_apply c d]
  apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

theorem complexWeight_trace_mul (a b c d : ℝ) :
    LinearMap.trace ℝ ℂ (complexWeight a b * complexWeight c d) = -2 * (a - b) * (c - d) := by
  have h : complexWeight a b * complexWeight c d = (-((a - b) * (c - d))) • LinearMap.id :=
    LinearMap.ext (complexWeight_comp_apply a b c d)
  rw [h, map_smul, LinearMap.trace_id, Complex.finrank_real_complex, smul_eq_mul]
  push_cast
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Compute a trace-normalized Casimir in an orthogonal basis of known squared norms. -/
theorem operatorCasimir_of_orthogonalBasis {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (T : Submodule ℝ (SkewOperator V)) (A : ι → T) (w : ι → ℝ)
    (hd : Module.finrank ℝ T = Fintype.card ι) (hw : ∀ i, 0 < w i)
    (hA : ∀ i j, ⟪A i, A j⟫ = if i = j then w i else 0) :
    operatorCasimir T = -∑ i, (w i)⁻¹ • ((A i).val.val * (A i).val.val) := by
  let s (i : ι) : ℝ := (Real.sqrt (w i))⁻¹
  have hs (i : ι) : s i * s i = (w i)⁻¹ := by
    dsimp [s]
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (hw i).le]
  let B (i : ι) := s i • A i
  have hB : Orthonormal ℝ B := by
    rw [orthonormal_iff_ite]
    intro i j
    have h' (i j : ι) : ⟪(A i).val, (A j).val⟫ = if i = j then w i else 0 := hA i j
    change ⟪s i • (A i).val, s j • (A j).val⟫ = _
    rw [real_inner_smul_left, real_inner_smul_right, h']
    split_ifs with h
    · subst j
      rw [← mul_assoc, hs, inv_mul_cancel₀ (hw i).ne']
    · ring
  let basis := OrthonormalBasis.mk hB (hB.linearIndependent.span_eq_top_of_card_eq_finrank hd.symm).ge
  rw [operatorCasimir_eq_sum T basis]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : basis i = B i := by simp [basis]
  rw [hi]
  change (s i • (A i).val.val) * (s i • (A i).val.val) = _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hs]

end

end ThirteenPlanes.Cartan
