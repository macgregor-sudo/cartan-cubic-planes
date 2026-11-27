module

public import ThirteenPlanes.Cartan.ComplexOperators
public import ThirteenPlanes.AlbertGrading.Grading.Complexification
public import Mathlib.LinearAlgebra.TensorProduct.Lift

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading
open scoped TensorProduct

noncomputable section

private abbrev J := Glennie.Albert

private def jcTensorMap : Complexified J →ₗ[ℂ] JC :=
  JC.ofLinear.liftBaseChange ℂ

@[simp] private theorem jcTensorMap_tmul (z : ℂ) (x : J) :
    jcTensorMap (z ⊗ₜ[ℝ] x) = z • JC.of x := rfl

private def tensorPart (f : ℂ →ₗ[ℝ] ℝ) : Complexified J →ₗ[ℝ] J :=
  (TensorProduct.lid ℝ J).toLinearMap.comp (TensorProduct.map f LinearMap.id)

@[simp] private theorem tensorPart_tmul (f : ℂ →ₗ[ℝ] ℝ) (z : ℂ) (x : J) :
    tensorPart f (z ⊗ₜ[ℝ] x) = f z • x := by simp [tensorPart]

private theorem jcTensorParts (x : Complexified J) :
    (jcTensorMap x).re = tensorPart Complex.reLm x ∧ (jcTensorMap x).im = tensorPart Complex.imLm x := by
  induction x using TensorProduct.inductionOn with
  | tmul z y => simp
  | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]

private theorem jcTensor_decompose (x : Complexified J) :
    (1 : ℂ) ⊗ₜ[ℝ] (jcTensorMap x).re + Complex.I ⊗ₜ[ℝ] (jcTensorMap x).im = x := by
  rw [(jcTensorParts x).1, (jcTensorParts x).2]
  induction x using TensorProduct.inductionOn with
  | tmul z y =>
    rw [tensorPart_tmul, tensorPart_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
    congr 1
    simpa [Algebra.smul_def, mul_comm] using Complex.re_add_im z
  | add x y hx hy =>
    rw [map_add, map_add, TensorProduct.tmul_add, TensorProduct.tmul_add, add_add_add_comm, hx, hy]

/-- The pair carrier and the tensor-product carrier are the same complexification. -/
def jcTensorEquiv : Complexified J ≃ₗ[ℂ] JC :=
  LinearEquiv.ofBijective jcTensorMap ⟨by
    intro x y h
    have hx := jcTensor_decompose x
    rw [h, jcTensor_decompose] at hx
    exact hx.symm, by
    intro z
    refine ⟨(1 : ℂ) ⊗ₜ[ℝ] z.re + Complex.I ⊗ₜ[ℝ] z.im, ?_⟩
    simpa only [map_add, jcTensorMap_tmul, one_smul] using (JC.eq_re_add_im z).symm⟩

@[simp] theorem jcTensorEquiv_tmul (z : ℂ) (x : J) :
    jcTensorEquiv (z ⊗ₜ[ℝ] x) = z • JC.of x := rfl

theorem jcTensorEquiv_mapC (A : Module.End ℝ J) :
    jcTensorEquiv.conj (A.baseChange ℂ) = JC.mapC A := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := jcTensorEquiv.surjective z
  change jcTensorEquiv ((A.baseChange ℂ) (jcTensorEquiv.symm (jcTensorEquiv x))) =
    JC.mapC A (jcTensorEquiv x)
  rw [jcTensorEquiv.symm_apply_apply]
  induction x using TensorProduct.inductionOn with
  | tmul c a => simp [JC.mapC_of]
  | add x y hx hy => simp [hx, hy]

/-- Transport the whole complexified operator, including its imaginary part. -/
theorem jcTensorEquiv_realImagOperator (A B : Module.End ℝ J) :
    jcTensorEquiv.conj (realImagOperator A B) = JC.mapC A + Complex.I • JC.mapC B := by
  rw [realImagOperator, map_add, map_smul, jcTensorEquiv_mapC, jcTensorEquiv_mapC]

theorem jcTraceForm_realImag (A B D E : Module.End ℝ J) :
    -LinearMap.trace ℂ JC ((JC.mapC A + Complex.I • JC.mapC B) *
        (JC.mapC D + Complex.I • JC.mapC E)) =
      ((-LinearMap.trace ℝ J (A * D) + LinearMap.trace ℝ J (B * E) : ℝ) : ℂ) -
      Complex.I * ((LinearMap.trace ℝ J (A * E) + LinearMap.trace ℝ J (B * D) : ℝ) : ℂ) := by
  rw [← jcTensorEquiv_realImagOperator, ← jcTensorEquiv_realImagOperator]
  let U := realImagOperator A B
  let V := realImagOperator D E
  have h : jcTensorEquiv.conj (U * V) = (jcTensorEquiv.conj U) * (jcTensorEquiv.conj V) :=
    LinearEquiv.conj_comp jcTensorEquiv V U
  change -(LinearMap.trace ℂ JC) ((jcTensorEquiv.conj U) * (jcTensorEquiv.conj V)) = _
  rw [← h, LinearMap.trace_conj' _ jcTensorEquiv]
  exact complexTraceForm_realImag A D B E

end
end ThirteenPlanes.Cartan
