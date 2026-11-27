module

public import ThirteenPlanes.RealDerivations.OrderThree
public import ThirteenPlanes.Peirce.SlotRealModel
public import ThirteenPlanes.Shares.ComplexCoordinates
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RealDerivations

open Peirce RoundCubics
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

abbrev V := RealTracelessSymmetric3

def trace : SymmetricThree →ₗ[ℝ] ℝ :=
  (Matrix.traceLinearMap (n := Fin 3) ℝ ℝ).comp (selfAdjoint.submodule ℝ M₃).subtype

@[simp] theorem trace_apply (x : SymmetricThree) : trace x = Matrix.trace x.val := rfl

theorem trace_one : trace 1 = 3 := by simp

def realTraceLinear : V →ₗ[ℝ] M₃ where
  toFun := realTraceMatrix
  map_add' x y := by
    change (fun i j => (TracelessHermitian3.toMatrix (x.val + y.val) i j).re) = _
    rw [map_add]
    ext i j
    simp only [Matrix.add_apply, Complex.add_re]
    rfl
  map_smul' r x := by
    change (fun i j => (TracelessHermitian3.toMatrix (r • x.val) i j).re) = _
    rw [map_smul]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rfl

def traceMatrix (x : V) : SymmetricThree :=
  ⟨realTraceMatrix x, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact ((realTraceMatrix_range _).mp ⟨x, rfl⟩).1⟩

def traceMatrixLinear : V →ₗ[ℝ] SymmetricThree where
  toFun := traceMatrix
  map_add' x y := Subtype.ext (realTraceLinear.map_add x y)
  map_smul' r x := Subtype.ext (realTraceLinear.map_smul r x)

theorem traceMatrix_trace (x : V) : trace (traceMatrix x) = 0 :=
  ((realTraceMatrix_range _).mp ⟨x, rfl⟩).2

def traceMatrixEquiv : V ≃ₗ[ℝ] trace.ker :=
  LinearEquiv.ofBijective (traceMatrixLinear.codRestrict trace.ker traceMatrix_trace) ⟨by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hz : (traceMatrix x).val = 0 := congrArg (fun t : trace.ker => t.val.val) hx
    have hi := realTraceMatrix_inner x x
    change ⟪x, x⟫ = Matrix.trace ((traceMatrix x).val * (traceMatrix x).val) at hi
    rw [hz, zero_mul, Matrix.trace_zero] at hi
    change x = (0 : RealTracelessSymmetric3)
    rw [real_inner_self_eq_norm_sq] at hi
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi), by
    intro x
    have hx := x.val.property
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hx
    obtain ⟨y, hy⟩ := (realTraceMatrix_range x.val.val).mpr ⟨hx, x.property⟩
    exact ⟨y, Subtype.ext (Subtype.ext hy)⟩⟩

theorem traceMatrixEquiv_apply (x : V) : (traceMatrixEquiv x).val = traceMatrix x := rfl

def centerLinear : SymmetricThree →ₗ[ℝ] SymmetricThree :=
  LinearMap.id - (LinearMap.toSpanSingleton ℝ SymmetricThree (1 : SymmetricThree)).comp ((1 / 3 : ℝ) • trace)

theorem centerLinear_apply (x : SymmetricThree) : centerLinear x = x - (trace x / 3) • 1 := by
  change x - ((1 / 3 : ℝ) * trace x) • 1 = _
  rw [one_div, mul_comm, ← div_eq_mul_inv]

theorem center_trace (x : SymmetricThree) : trace (centerLinear x) = 0 := by
  rw [centerLinear_apply, map_sub, map_smul, trace_one, smul_eq_mul]
  ring

def readTraceZero : SymmetricThree →ₗ[ℝ] V :=
  traceMatrixEquiv.symm.toLinearMap.comp (centerLinear.codRestrict trace.ker center_trace)

theorem traceMatrix_readTraceZero (x : SymmetricThree) :
    traceMatrix (readTraceZero x) = centerLinear x := by
  rw [← traceMatrixEquiv_apply]
  exact congrArg Subtype.val (traceMatrixEquiv.apply_symm_apply ⟨centerLinear x, center_trace x⟩)

theorem readTraceZero_traceMatrix (x : V) : readTraceZero (traceMatrix x) = x := by
  apply traceMatrixEquiv.injective
  apply Subtype.ext
  rw [traceMatrixEquiv_apply, traceMatrixEquiv_apply, traceMatrix_readTraceZero, centerLinear_apply,
    traceMatrix_trace, zero_div, zero_smul, sub_zero]

def jordanLinear : SymmetricThree →ₗ[ℝ] SymmetricThree →ₗ[ℝ] SymmetricThree :=
  LinearMap.mk₂ ℝ jordan
    (fun x y z => Subtype.ext (by
      change (1 / 2 : ℝ) • ((x.val + y.val) * z.val + z.val * (x.val + y.val)) = _
      simp only [jordan, AddSubgroup.coe_add, add_mul, mul_add, smul_add]
      abel))
    (fun r x y => Subtype.ext (by
      change (1 / 2 : ℝ) • ((r • x.val) * y.val + y.val * (r • x.val)) = r • ((1 / 2 : ℝ) • _)
      rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_comm]))
    (fun x y z => Subtype.ext (by
      change (1 / 2 : ℝ) • (x.val * (y.val + z.val) + (y.val + z.val) * x.val) = _
      simp only [jordan, AddSubgroup.coe_add, add_mul, mul_add, smul_add]
      abel))
    (fun r x y => Subtype.ext (by
      change (1 / 2 : ℝ) • (x.val * (r • y.val) + (r • y.val) * x.val) = r • ((1 / 2 : ℝ) • _)
      rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_comm]))

private theorem prod_inner (x y z : V) :
    ⟪readTraceZero (jordan (traceMatrix x) (traceMatrix y)), z⟫ =
      Matrix.trace ((jordan (traceMatrix x) (traceMatrix y)).val * (traceMatrix z).val) := by
  rw [realTraceMatrix_inner]
  change Matrix.trace ((traceMatrix (readTraceZero _)).val * (traceMatrix z).val) = _
  rw [traceMatrix_readTraceZero, centerLinear_apply]
  change Matrix.trace (((jordan (traceMatrix x) (traceMatrix y)).val -
    (trace (jordan (traceMatrix x) (traceMatrix y)) / 3) • (1 : M₃)) * (traceMatrix z).val) = _
  rw [sub_mul, smul_mul_assoc, one_mul, Matrix.trace_sub, Matrix.trace_smul]
  have hz : Matrix.trace (traceMatrix z).val = 0 := traceMatrix_trace z
  rw [hz, smul_zero, sub_zero]

private theorem trace_Jordan_swap (x y z : SymmetricThree) :
    Matrix.trace ((jordan x y).val * z.val) = Matrix.trace ((jordan x z).val * y.val) := by
  change Matrix.trace (((1 / 2 : ℝ) • (x.val * y.val + y.val * x.val)) * z.val) =
    Matrix.trace (((1 / 2 : ℝ) • (x.val * z.val + z.val * x.val)) * y.val)
  rw [smul_mul_assoc, smul_mul_assoc, add_mul, add_mul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_add]
  have hy := (Matrix.trace_mul_cycle y.val x.val z.val).trans (Matrix.trace_mul_cycle z.val y.val x.val)
  rw [hy, ← Matrix.trace_mul_cycle x.val y.val z.val]
  ring

private def traceProduct : V →ₗ[ℝ] V →ₗ[ℝ] V :=
  (LinearMap.llcomp ℝ _ _ _ readTraceZero).comp (jordanLinear.compl₁₂ traceMatrixLinear traceMatrixLinear)

private def rawCubic : SymmetricCubic V := SymmetricCubic.ofProduct traceProduct
  (fun x y => congrArg readTraceZero (Subtype.ext (by
    change (1 / 2 : ℝ) • _ = (1 / 2 : ℝ) • _
    rw [add_comm])))
  (fun x y z => by
    change ⟪readTraceZero (jordan (traceMatrix x) (traceMatrix y)), z⟫ =
      ⟪readTraceZero (jordan (traceMatrix x) (traceMatrix z)), y⟫
    rw [prod_inner, prod_inner, trace_Jordan_swap])

private theorem diagonal_ext {h k : SymmetricCubic V}
    (he : ∀ x, h.apply x x x = k.apply x x x) : h = k := by
  apply SymmetricCubic.ext
  intro x y z
  have hh := threeInputCubic_eq h x y z
  rw [he, he, he, he, he, he, he, threeInputCubic_eq] at hh
  linarith

theorem realCartan_product (x y : V) :
    realCartanCubic.L x y = Real.sqrt 6 • readTraceZero (jordan (traceMatrix x) (traceMatrix y)) := by
  have hh : realCartanCubic = Real.sqrt 6 • rawCubic := by
    apply diagonal_ext
    intro u
    rw [realCartanCubic_diagonal, SymmetricCubic.apply_smul]
    change Real.sqrt 6 * Matrix.trace ((realTraceMatrix u) ^ 3) =
      Real.sqrt 6 * ⟪readTraceZero (jordan (traceMatrix u) (traceMatrix u)), u⟫
    rw [prod_inner]
    change _ = Real.sqrt 6 * Matrix.trace
      (((1 / 2 : ℝ) • ((realTraceMatrix u) * realTraceMatrix u + (realTraceMatrix u) * realTraceMatrix u)) *
        realTraceMatrix u)
    rw [← two_smul ℝ ((realTraceMatrix u) * realTraceMatrix u), smul_smul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul, pow_succ, pow_two]
  rw [hh, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  rfl

end

end ThirteenPlanes.RealDerivations
