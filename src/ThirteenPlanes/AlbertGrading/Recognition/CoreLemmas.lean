module

public import ThirteenPlanes.AlbertGrading.Recognition.Four
public import ThirteenPlanes.AlbertGrading.Recognition.Recognition
public import ThirteenPlanes.AlbertGrading.Tits.ExteriorMain

@[expose] public section

set_option backward.privateInPublic true

/-!
# Lemmas in `J_T` for recognition of systems with 52 positive shares

The unit, the trace form and its coefficients, automorphisms carrying systems of frames, and the
complexified product space of two graded planes.
-/

open scoped Matrix BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-! ## The unit and the trace -/

theorem firstTitsJordanProduct_one_left (y : FirstTits ℂ) : firstTitsJordanProduct firstTitsOne y = y := by
  obtain ⟨A, B, C⟩ := y
  have h3 : trace3 (1 : Mat3 ℂ) = 3 := by norm_num [trace3]
  have h0 : trace3 (0 : Mat3 ℂ) = 0 := by simp [trace3]
  simp only [firstTitsJordanProduct, firstTitsOne, sharpPair, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, h3, h0, smul_zero, sub_zero, mul_zero,
    zero_smul, zero_sub]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> module

theorem product_one_left (x : CompactTits) : CompactTits.product CompactTits.one x = x :=
  CompactTits.ext (by rw [coordinates_product, CompactTits.coordinates_one, firstTitsJordanProduct_one_left])

theorem product_comm' (x y : CompactTits) : CompactTits.product x y = CompactTits.product y x :=
  CompactTits.ext (by rw [coordinates_product, coordinates_product, firstTitsJordanProduct_comm])

/-- An automorphism of `J_T` that preserves the trace. -/
def IsTraceAut (f : CompactTits ≃ₗ[ℝ] CompactTits) : Prop :=
  IsTitsAutomorphism f ∧ ∀ x, CompactTits.trace (f x) = CompactTits.trace x

theorem IsTraceAut.map_one {f : CompactTits ≃ₗ[ℝ] CompactTits} (hf : IsTraceAut f) :
    f CompactTits.one = CompactTits.one := by
  have h := hf.1 CompactTits.one (f.symm CompactTits.one)
  rw [product_one_left, LinearEquiv.apply_symm_apply, product_comm', product_one_left] at h
  exact h.symm

theorem IsTraceAut.trans {f f' : CompactTits ≃ₗ[ℝ] CompactTits} (hf : IsTraceAut f)
    (hf' : IsTraceAut f') : IsTraceAut (f.trans f') :=
  ⟨fun x y => by simp only [LinearEquiv.trans_apply]; rw [hf.1, hf'.1],
    fun x => by simp only [LinearEquiv.trans_apply, hf.2, hf'.2]⟩

theorem IsTraceAut.symm {f : CompactTits ≃ₗ[ℝ] CompactTits} (hf : IsTraceAut f) :
    IsTraceAut f.symm :=
  ⟨fun x y => f.injective (by rw [hf.1]; simp),
    fun x => by rw [← hf.2 (f.symm x), LinearEquiv.apply_symm_apply]⟩

theorem trace_product_eq_inner (x y : CompactTits) :
    CompactTits.trace (CompactTits.product x y) = ⟪x, y⟫ := by
  have h : CompactTits.trace (CompactTits.product x y) =
      (1 / 2) * (‖x + y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) := by
    rw [CompactTits.product, map_smul, map_sub, map_sub, CompactTits.trace_square,
      CompactTits.trace_square, CompactTits.trace_square, smul_eq_mul]
  rw [h, norm_add_sq_real]; ring

theorem complex_trace_product (x y : CompactTits) :
    ((CompactTits.trace (CompactTits.product x y) : ℝ) : ℂ) =
      titsTraceForm (CompactTits.coordinates x) (CompactTits.coordinates y) := by
  rw [trace_product_eq_inner, CompactTits.complexTrace_eq_inner]; rfl

/-! ## The complex trace form and coefficients -/

private theorem trace3_add'' (a b : Mat3 ℂ) : trace3 (a + b) = trace3 a + trace3 b := by
  simp only [trace3, Matrix.add_apply]; ring

private theorem trace3_smul'' (c : ℂ) (a : Mat3 ℂ) : trace3 (c • a) = c * trace3 a := by
  simp only [trace3, Matrix.smul_apply, smul_eq_mul]; ring

/-- The trace form `T(,)` as a complex bilinear map. -/
def traceBilin : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ titsTraceForm
    (fun x x' y => by
      simp only [titsTraceForm, Prod.fst_add, Prod.snd_add, Matrix.add_mul, trace3_add'']; ring)
    (fun c x y => by
      simp only [titsTraceForm, Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, trace3_smul'']
      ring)
    (fun x y y' => by
      simp only [titsTraceForm, Prod.fst_add, Prod.snd_add, Matrix.mul_add, trace3_add'']; ring)
    (fun c x y => by
      simp only [titsTraceForm, Prod.smul_fst, Prod.smul_snd, Matrix.mul_smul, trace3_smul'']
      ring)

@[simp] theorem traceBilin_apply (x y : FirstTits ℂ) : traceBilin x y = titsTraceForm x y := rfl

theorem basis_expansion (x : FirstTits ℂ) : x = ∑ g, coef g x • titsBasis g := by
  conv_lhs => rw [← gradedTitsComplexEquiv.apply_symm_apply x]
  rw [pi_eq_sum_univ (gradedTitsComplexEquiv.symm x), map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, titsBasis_eq_equiv]
  congr 2
  funext y
  simp [chargeBasisVector, eq_comm]

theorem traceForm_titsBasis_right (x : FirstTits ℂ) (h : Charge) :
    titsTraceForm x (titsBasis h) = 3 * coef (-h) x := by
  rw [← traceBilin_apply]
  conv_lhs => rw [basis_expansion x]
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, traceBilin_apply, titsBasis_traceForm, smul_eq_mul,
    mul_ite, mul_zero]
  rw [Finset.sum_eq_single (-h)]
  · rw [if_pos (neg_add_cancel h)]; ring
  · intro b _ hb
    rw [if_neg]
    intro e; exact hb (eq_neg_of_add_eq_zero_left e)
  · simp

theorem weylD_zero : weylD (0, 0) = 1 := by simp [weylD]

/-- If all coefficients on `u_{(v,0)}`, `v ≠ 0`, vanish, the first matrix is `coef 0 x • 1`. -/
theorem first_of_coef (x : FirstTits ℂ)
    (h : ∀ v : WeylLabel, v ≠ 0 → coef (chargeFrom v 0) x = 0) :
    x.1 = coef 0 x • (1 : Mat3 ℂ) := by
  have hx := basis_expansion x
  have h1 : x.1 = ∑ g, coef g x • (titsBasis g).1 := by
    conv_lhs => rw [hx]
    simp [Prod.fst_sum]
  rw [h1, ← chargeComponentEquiv.sum_comp]
  simp only [chargeComponentEquiv, Equiv.coe_fn_mk]
  rw [Fintype.sum_prod_type, sum_zmod3]
  have hz1 : ∀ v : WeylLabel, (titsBasis (chargeFrom v 1)).1 = 0 := by
    intro v; simp [titsBasis, iota, show (1 : ZMod 3) ≠ 0 by decide]
  have hz2 : ∀ v : WeylLabel, (titsBasis (chargeFrom v 2)).1 = 0 := by
    intro v; simp [titsBasis, iota, show (2 : ZMod 3) ≠ 0 by decide]
  simp only [hz1, hz2, smul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single (0 : WeylLabel)]
  · rw [chargeFrom_zero, titsBasis_zero]; rfl
  · intro v _ hv; rw [h v hv, zero_smul]
  · simp

end

end ThirteenPlanes.AlbertGrading
