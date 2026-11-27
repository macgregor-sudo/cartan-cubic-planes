module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

set_option backward.privateInPublic true

/-! Real and imaginary parts in the scalar extension of a real Lie algebra. -/

namespace ThirteenPlanes.Cartan

open scoped TensorProduct
open LieAlgebra

noncomputable section

abbrev LieComplex (K : Type*) [LieRing K] [LieAlgebra ℝ K] := ℂ ⊗[ℝ] K

namespace LieComplex

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K]

/-- The homomorphism embedding the real Lie algebra into its complexification. -/
def ofReal : K →ₗ⁅ℝ⁆ LieComplex K :=
  { TensorProduct.mk ℝ ℂ K 1 with
    map_lie' := by simp [ExtendScalars.bracket_tmul] }

@[simp] theorem ofReal_apply (x : K) : ofReal x = (1 : ℂ) ⊗ₜ[ℝ] x := rfl

private def coordinate (f : ℂ →ₗ[ℝ] ℝ) : LieComplex K →ₗ[ℝ] K :=
  (TensorProduct.lid ℝ K).toLinearMap.comp (TensorProduct.map f LinearMap.id)

/-- Real coordinate of the tensor product. -/
def realPart : LieComplex K →ₗ[ℝ] K := coordinate Complex.reLm

/-- Imaginary coordinate of the tensor product. -/
def imagPart : LieComplex K →ₗ[ℝ] K := coordinate Complex.imLm

@[simp] theorem realPart_tmul (z : ℂ) (x : K) :
    realPart (z ⊗ₜ[ℝ] x) = z.re • x := by simp [realPart, coordinate]

@[simp] theorem imagPart_tmul (z : ℂ) (x : K) :
    imagPart (z ⊗ₜ[ℝ] x) = z.im • x := by simp [imagPart, coordinate]

@[simp] theorem realPart_ofReal (x : K) : realPart (ofReal x) = x := by simp

@[simp] theorem imagPart_ofReal (x : K) : imagPart (ofReal x) = 0 := by simp

theorem ofReal_injective : Function.Injective (ofReal : K → LieComplex K) :=
  fun _ _ h => by simpa using congrArg realPart h

@[simp] theorem realPart_I_tmul (x : K) : realPart (Complex.I ⊗ₜ[ℝ] x) = 0 := by simp

@[simp] theorem imagPart_I_tmul (x : K) : imagPart (Complex.I ⊗ₜ[ℝ] x) = x := by simp

theorem decompose (x : LieComplex K) :
    ofReal (realPart x) + Complex.I ⊗ₜ[ℝ] imagPart x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    rw [realPart_tmul, imagPart_tmul, ofReal_apply, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul]
    congr 1
    simpa [Algebra.smul_def, mul_comm] using Complex.re_add_im z
  | add x y hx hy =>
    rw [map_add, map_add, map_add, TensorProduct.tmul_add, add_add_add_comm, hx, hy]

theorem decompose_smul (x : LieComplex K) :
    ofReal (realPart x) + Complex.I • ofReal (imagPart x) = x := by
  simpa [TensorProduct.smul_tmul'] using decompose x

theorem bracket_parts (a b c d : K) :
    ⁅ofReal a + Complex.I ⊗ₜ[ℝ] b, ofReal c + Complex.I ⊗ₜ[ℝ] d⁆ =
      ofReal (⁅a,c⁆ - ⁅b,d⁆) + Complex.I ⊗ₜ[ℝ] (⁅a,d⁆ + ⁅b,c⁆) := by
  simp only [ofReal_apply, add_lie, lie_add, ExtendScalars.bracket_tmul, one_mul, mul_one,
    Complex.I_mul_I, TensorProduct.tmul_sub, TensorProduct.tmul_add, TensorProduct.neg_tmul]
  abel

theorem realPart_bracket (x y : LieComplex K) :
    realPart ⁅x,y⁆ = ⁅realPart x, realPart y⁆ - ⁅imagPart x, imagPart y⁆ := by
  conv_lhs => rw [← decompose x, ← decompose y]
  simp only [bracket_parts, map_add, realPart_ofReal, realPart_I_tmul, add_zero]

theorem imagPart_bracket (x y : LieComplex K) :
    imagPart ⁅x,y⁆ = ⁅realPart x, imagPart y⁆ + ⁅imagPart x, realPart y⁆ := by
  conv_lhs => rw [← decompose x, ← decompose y]
  simp only [bracket_parts, map_add, imagPart_ofReal, imagPart_I_tmul, zero_add]

theorem realPart_smul (z : ℂ) (x : LieComplex K) :
    realPart (z • x) = z.re • realPart x - z.im • imagPart x := by
  induction x using TensorProduct.inductionOn with
  | tmul w x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, realPart_tmul, Complex.mul_re,
      realPart_tmul, imagPart_tmul, sub_smul, smul_smul, smul_smul]
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]
    abel

theorem imagPart_smul (z : ℂ) (x : LieComplex K) :
    imagPart (z • x) = z.re • imagPart x + z.im • realPart x := by
  induction x using TensorProduct.inductionOn with
  | tmul w x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, imagPart_tmul, Complex.mul_im,
      realPart_tmul, imagPart_tmul, add_smul, smul_smul, smul_smul]
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]
    abel

@[simp] theorem realPart_real_smul (r : ℝ) (x : LieComplex K) :
    realPart (r • x) = r • realPart x := map_smul _ _ _

@[simp] theorem imagPart_real_smul (r : ℝ) (x : LieComplex K) :
    imagPart (r • x) = r • imagPart x := map_smul _ _ _

/-- Conjugation extending complex conjugation on the scalar factor. -/
def conjugation : LieComplex K →ₗ⁅ℝ⁆ LieComplex K :=
  ExtendScalars.map Complex.conjAe.toAlgHom (LieHom.id : K →ₗ⁅ℝ⁆ K)

@[simp] theorem conjugation_tmul (z : ℂ) (x : K) :
    conjugation (z ⊗ₜ[ℝ] x) = (star z) ⊗ₜ[ℝ] x := by
  simp [conjugation]

@[simp] theorem conjugation_ofReal (x : K) : conjugation (ofReal x) = ofReal x := by simp

theorem conjugation_decompose (x : LieComplex K) :
    conjugation x = ofReal (realPart x) - Complex.I • ofReal (imagPart x) := by
  conv_lhs => rw [← decompose x]
  simp [TensorProduct.smul_tmul', sub_eq_add_neg, Complex.conj_I, TensorProduct.neg_tmul]

end LieComplex
end
end ThirteenPlanes.Cartan
