module

public import ThirteenPlanes.RealDerivations.TraceBridge

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RealDerivations

open Peirce
open scoped Matrix RealInnerProductSpace

noncomputable section

private theorem decompose (x : SymmetricThree) : x =
    traceMatrix (readTraceZero x) + (trace x / 3) • 1 := by
  rw [traceMatrix_readTraceZero, centerLinear_apply, sub_add_cancel]

private theorem readTraceZero_one : readTraceZero 1 = 0 := by
  apply traceMatrixEquiv.injective
  apply Subtype.ext
  rw [traceMatrixEquiv_apply, traceMatrix_readTraceZero, centerLinear_apply, trace_one]
  change (1 : SymmetricThree) - (3 / 3 : ℝ) • 1 = traceMatrixLinear 0
  rw [map_zero]
  norm_num

private theorem jl_one (x : SymmetricThree) : jordanLinear 1 x = x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (1 * x.val + x.val * 1) = x.val
  rw [one_mul, mul_one, ← two_smul ℝ x.val, smul_smul]
  norm_num

private theorem jr_one (x : SymmetricThree) : jordanLinear x 1 = x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (x.val * 1 + 1 * x.val) = x.val
  rw [one_mul, mul_one, ← two_smul ℝ x.val, smul_smul]
  norm_num

private theorem trace_jordan (x y : SymmetricThree) :
    trace (jordan x y) = Matrix.trace (x.val * y.val) := by
  change Matrix.trace ((1 / 2 : ℝ) • (x.val * y.val + y.val * x.val)) = _
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_comm y.val x.val, smul_eq_mul]
  ring

/-- A skew derivation of the traceless cubic product extends to the unital matrix
algebra by taking zero on its unit. -/
theorem realTraceDerivation_inner (D : Module.End ℝ V)
    (hd : ∀ x y, D (realCartanCubic.L x y) =
      realCartanCubic.L (D x) y + realCartanCubic.L x (D y))
    (hs : ∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫) :
    ∃ (T : M₃) (_ : Tᵀ = -T), ∀ x : V,
      realTraceMatrix (D x) = T * realTraceMatrix x - realTraceMatrix x * T := by
  let E : Module.End ℝ SymmetricThree := traceMatrixLinear.comp (D.comp readTraceZero)
  have e_apply (x : SymmetricThree) : E x = traceMatrix (D (readTraceZero x)) := rfl
  have he (x : V) : E (traceMatrix x) = traceMatrix (D x) := by
    rw [e_apply, readTraceZero_traceMatrix]
  have he₁ : E 1 = 0 := by rw [e_apply, readTraceZero_one, map_zero]; exact map_zero traceMatrixLinear
  have hc (x y : V) :
      D (readTraceZero (jordan (traceMatrix x) (traceMatrix y))) =
        readTraceZero (jordan (traceMatrix (D x)) (traceMatrix y)) +
          readTraceZero (jordan (traceMatrix x) (traceMatrix (D y))) := by
    have h := hd x y
    simp only [realCartan_product, map_smul, ← smul_add] at h
    exact (smul_right_injective V (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne') h
  have hc' (x y : V) :
      E (jordan (traceMatrix x) (traceMatrix y)) =
        jordan (E (traceMatrix x)) (traceMatrix y) + jordan (traceMatrix x) (E (traceMatrix y)) := by
    rw [e_apply, hc, he, he]
    have hsplit (X Y : SymmetricThree) :
        traceMatrix (readTraceZero X + readTraceZero Y) = centerLinear X + centerLinear Y := by
      change traceMatrixLinear (readTraceZero X + readTraceZero Y) = _
      rw [map_add]
      exact congrArg₂ (· + ·) (traceMatrix_readTraceZero X) (traceMatrix_readTraceZero Y)
    rw [hsplit, centerLinear_apply, centerLinear_apply]
    have htr : trace (jordan (traceMatrix (D x)) (traceMatrix y)) +
        trace (jordan (traceMatrix x) (traceMatrix (D y))) = 0 := by
      rw [trace_jordan, trace_jordan]
      change Matrix.trace (realTraceMatrix (D x) * realTraceMatrix y) +
        Matrix.trace (realTraceMatrix x * realTraceMatrix (D y)) = 0
      rw [← realTraceMatrix_inner, ← realTraceMatrix_inner, hs, neg_add_cancel]
    rw [sub_add_sub_comm, ← add_smul, ← add_div, htr, zero_div, zero_smul, sub_zero]
  have hE : Derivation E := by
    intro x y
    obtain ⟨u, r, rfl⟩ : ∃ u : V, ∃ r : ℝ, traceMatrix u + r • 1 = x :=
      ⟨readTraceZero x, trace x / 3, (decompose x).symm⟩
    obtain ⟨v, s, rfl⟩ : ∃ v : V, ∃ s : ℝ, traceMatrix v + s • 1 = y :=
      ⟨readTraceZero y, trace y / 3, (decompose y).symm⟩
    change E (jordanLinear (traceMatrix u + r • 1) (traceMatrix v + s • 1)) =
      jordanLinear (E (traceMatrix u + r • 1)) (traceMatrix v + s • 1) +
      jordanLinear (traceMatrix u + r • 1) (E (traceMatrix v + s • 1))
    have hh := hc' u v
    change E (jordanLinear (traceMatrix u) (traceMatrix v)) =
      jordanLinear (E (traceMatrix u)) (traceMatrix v) +
      jordanLinear (traceMatrix u) (E (traceMatrix v)) at hh
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, jl_one, jr_one,
      he₁, smul_zero, add_zero, hh]
    abel
  obtain ⟨T, hT, hC⟩ := real_symmetric_derivation_inner E hE
  refine ⟨T, hT, fun x => ?_⟩
  have hmat := congrArg (fun u : SymmetricThree => u.val) (he x)
  rw [hC, commutator_apply] at hmat
  exact hmat.symm

end
end ThirteenPlanes.RealDerivations
