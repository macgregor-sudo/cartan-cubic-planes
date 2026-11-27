module

public import ThirteenPlanes.Cartan.SecondRowLieRealization
public import ThirteenPlanes.Cartan.SecondRowLieMetricComparison
public import ThirteenPlanes.Cartan.ComplexCasimir
public import Mathlib.LinearAlgebra.TensorProduct.Lift

@[expose] public section

set_option backward.privateInPublic true

/-! The two complex second-row factors are exchanged by the native conjugation. -/

namespace ThirteenPlanes.Cartan

open RoundCubics
open scoped Matrix TensorProduct

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev S := secondRowCompactSU 3
private abbrev E := Complexified FullHermitian

private def skewCoord : complexSkewTracelessMatrices ≃ₗ[ℝ] S :=
  LinearEquiv.ofEq _ _ rfl

private def commutatorCoord : S ≃ₗ[ℝ] complexOperatorAlgebra :=
  skewCoord.symm.trans (LinearEquiv.ofInjective complexCommutatorLinear
    complexCommutatorLinear_injective)

private lemma skew_trace_free (A : complexJordan.traceFree) : Matrix.trace (fullMatrix A.val) = 0 := by
  rw [hermitian_trace_eq_real (fullMatrix_hermitian A.val), ← complexJordan_trace]
  exact_mod_cast (show complexJordan.trace A.val = 0 from A.property)

private lemma halfImag_mem (A : complexJordan.traceFree) :
    ((Complex.I / 2) • fullMatrix A.val) ∈ S := by
  change ((Complex.I / 2) • fullMatrix A.val)ᴴ = -((Complex.I / 2) • fullMatrix A.val) ∧
    Matrix.trace ((Complex.I / 2) • fullMatrix A.val) = 0
  constructor
  · rw [Matrix.conjTranspose_smul, (fullMatrix_hermitian A.val).eq, ← neg_smul]
    congr 1
    simp [div_eq_mul_inv]
  · rw [Matrix.trace_smul, skew_trace_free, smul_zero]

private def fromHalfImag (A : S) : complexJordan.traceFree :=
  ⟨ofFullMatrix ((-2 * Complex.I) • A.val) (by
      change ((-2 * Complex.I) • A.val)ᴴ = _
      have hA : A.valᴴ = -A.val := A.property.1
      rw [Matrix.conjTranspose_smul, hA, smul_neg, ← neg_smul]
      congr 1
      simp),
    by
      change complexJordan.trace (ofFullMatrix _ _) = 0
      rw [complexJordan_trace, fullMatrix_ofFullMatrix, Matrix.trace_smul,
        (show Matrix.trace A.val = 0 from A.property.2), smul_zero, Complex.zero_re]⟩

private lemma fromHalfImag_matrix (A : S) :
    fullMatrix (fromHalfImag A).val = (-2 * Complex.I) • A.val := rfl

private def halfImag : complexJordan.traceFree ≃ₗ[ℝ] S where
  toFun A := ⟨_, halfImag_mem A⟩
  invFun := fromHalfImag
  left_inv A := by
    apply Subtype.ext
    apply fullMatrix_injective
    rw [fromHalfImag_matrix]
    change (-2 * Complex.I) • ((Complex.I / 2) • fullMatrix A.val) = _
    rw [smul_smul, show (-2 * Complex.I) * (Complex.I / 2) = 1 by
      rw [← mul_div_assoc, mul_assoc, Complex.I_mul_I]; norm_num, one_smul]
  right_inv A := by
    apply Subtype.ext
    change (Complex.I / 2) • fullMatrix (fromHalfImag A).val = A.val
    rw [fromHalfImag_matrix, smul_smul, mul_comm (Complex.I / 2),
      show (-2 * Complex.I) * (Complex.I / 2) = 1 by
        rw [← mul_div_assoc, mul_assoc, Complex.I_mul_I]; norm_num, one_smul]
  map_add' A B := by
    apply Subtype.ext
    change (Complex.I / 2) • fullMatrix (A.val + B.val) =
      (Complex.I / 2) • fullMatrix A.val + (Complex.I / 2) • fullMatrix B.val
    rw [map_add, smul_add]
  map_smul' r A := by
    apply Subtype.ext
    change (Complex.I / 2) • fullMatrix (r • A.val) = r • ((Complex.I / 2) • fullMatrix A.val)
    rw [map_smul, smul_comm]

private def sumDifference : (S × S) ≃ₗ[ℝ] (S × S) where
  toFun p := (p.1 + p.2, p.1 - p.2)
  invFun p := ((1 / 2 : ℝ) • (p.1 + p.2), (1 / 2 : ℝ) • (p.1 - p.2))
  left_inv p := by
    apply Prod.ext <;> simp only [smul_add, smul_sub] <;> module
  right_inv p := by
    apply Prod.ext <;> simp only [smul_add, smul_sub] <;> module
  map_add' p q := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' r p := by
    apply Prod.ext <;> simp [smul_add, smul_sub]

private def factorCoordinates :
    secondRowSpace complexJordan complexOperatorAlgebra ≃ₗ[ℝ] S × S :=
  (secondRowCoordinates complexJordan complexOperatorAlgebra).symm.trans
    ((commutatorCoord.symm.prodCongr halfImag).trans sumDifference)

private theorem factorCoordinates_apply (A : S) (x : complexJordan.traceFree) :
    factorCoordinates (secondRowCoordinates complexJordan complexOperatorAlgebra (commutatorCoord A, x)) =
      (A + halfImag x, A - halfImag x) := by
  simp only [factorCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply]
  rfl

private def matrixComplexification : E →ₗ[ℂ] ComplexMatrix3 := fullMatrix.liftBaseChange ℂ

@[simp] private theorem matrixComplexification_tmul (z : ℂ) (A : FullHermitian) :
    matrixComplexification (z ⊗ₜ[ℝ] A) = z • fullMatrix A := rfl

private theorem matrixComplexification_injective : Function.Injective matrixComplexification := by
  have split (u : E) :
      ∃ x y : FullHermitian, u = (1 : ℂ) ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] y := by
    induction u using TensorProduct.inductionOn with
    | tmul z A =>
      refine ⟨z.re • A, z.im • A, ?_⟩
      rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
      congr 1
      simpa [Algebra.smul_def, mul_comm] using (Complex.re_add_im z).symm
    | add u v hu hv =>
      obtain ⟨a, b, rfl⟩ := hu
      obtain ⟨c, d, rfl⟩ := hv
      exact ⟨a + c, b + d, by simp only [TensorProduct.tmul_add]; abel⟩
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro u hu
  obtain ⟨x, y, rfl⟩ := split u
  simp only [map_add, matrixComplexification_tmul, one_smul] at hu
  have hv := congrArg Matrix.conjTranspose hu
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, (fullMatrix_hermitian x).eq,
    (fullMatrix_hermitian y).eq, Complex.star_def, Complex.conj_I, neg_smul,
    Matrix.conjTranspose_zero] at hv
  have hx : (2 : ℂ) • fullMatrix x = 0 := by
    calc
      _ = (fullMatrix x + Complex.I • fullMatrix y) +
          (fullMatrix x + -(Complex.I • fullMatrix y)) := by rw [two_smul]; abel
      _ = _ := by rw [hu, hv, add_zero]
  have hy : (2 : ℂ) • (Complex.I • fullMatrix y) = 0 := by
    calc
      _ = (fullMatrix x + Complex.I • fullMatrix y) -
          (fullMatrix x + -(Complex.I • fullMatrix y)) := by rw [two_smul]; abel
      _ = _ := by rw [hu, hv, sub_zero]
  have x0 : x = 0 := fullMatrix_injective (by
    rw [map_zero]
    exact (smul_eq_zero.mp hx).resolve_left (by norm_num))
  have y0 : y = 0 := fullMatrix_injective (by
    rw [map_zero]
    exact (smul_eq_zero.mp ((smul_eq_zero.mp hy).resolve_left (by norm_num))).resolve_left Complex.I_ne_zero)
  simp [x0, y0]

private theorem operator_matrix (U : secondRowSpace complexJordan complexOperatorAlgebra) (z : E) :
    matrixComplexification (U.val z) =
      (factorCoordinates U).1.val * matrixComplexification z -
        matrixComplexification z * (factorCoordinates U).2.val := by
  obtain ⟨⟨D, x⟩, rfl⟩ := (secondRowCoordinates complexJordan complexOperatorAlgebra).surjective U
  obtain ⟨A, rfl⟩ := commutatorCoord.surjective D
  rw [factorCoordinates_apply]
  change matrixComplexification (realImagOperator (complexCommutator (skewCoord.symm A))
    (complexJordan.L x.val) z) = _
  induction z using TensorProduct.inductionOn with
  | tmul c y =>
    simp only [realImagOperator, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
      map_add, map_smul, matrixComplexification_tmul, complexCommutator_matrix]
    change c • (A.val * fullMatrix y - fullMatrix y * A.val) +
      Complex.I • (c • fullMatrix (complexFullCubic.L x.val y)) =
      (A.val + (Complex.I / 2) • fullMatrix x.val) * (c • fullMatrix y) -
        (c • fullMatrix y) * (A.val - (Complex.I / 2) • fullMatrix x.val)
    rw [fullMatrix_complexFullCubic_product]
    simp only [symmetricMatrixProduct, add_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul,
      smul_sub, smul_add, smul_smul]
    rw [show Complex.I * (c * (1 / 2 : ℂ)) = c * (Complex.I / 2) by ring,
      mul_comm (Complex.I / 2) c]
    abel
  | add u v hu hv =>
    simp only [map_add, mul_add, add_mul, hu, hv]
    abel

variable (D : LieSubalgebra ℝ (Module.End ℂ E))
  (hD : D.toSubmodule = secondRowSpace complexJordan complexOperatorAlgebra)

private def coordOnSpace : D ≃ₗ[ℝ] secondRowSpace complexJordan complexOperatorAlgebra :=
  LinearEquiv.ofEq _ _ hD

/-- The actual complexification operators have the two native compact matrix factors. -/
def complexSecondRowFactorEquiv : D ≃ₗ⁅ℝ⁆ (secondRowCompactSU 3 × secondRowCompactSU 3) := by
  let f := (coordOnSpace D hD).trans factorCoordinates
  refine { f with map_lie' := ?_ }
  intro U V
  let W := f.symm ⁅f U, f V⁆
  have hW : f W = ⁅f U, f V⁆ := f.apply_symm_apply _
  change f ⁅U, V⁆ = ⁅f U, f V⁆
  rw [← hW]
  apply congrArg f
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  apply matrixComplexification_injective
  change matrixComplexification (U.val (V.val z) - V.val (U.val z)) =
    matrixComplexification ((coordOnSpace D hD W).val z)
  rw [map_sub]
  have act (P : D) (y : E) :
      matrixComplexification (P.val y) =
        (f P).1.val * matrixComplexification y - matrixComplexification y * (f P).2.val :=
    operator_matrix (coordOnSpace D hD P) y
  rw [act U, act V, act V, act U, operator_matrix, show
    factorCoordinates (coordOnSpace D hD W) = ⁅f U, f V⁆ from hW]
  change _ =
    ((f U).1.val * (f V).1.val - (f V).1.val * (f U).1.val) * matrixComplexification z -
      matrixComplexification z * ((f U).2.val * (f V).2.val - (f V).2.val * (f U).2.val)
  noncomm_ring

/-- The actual second-row conjugation swaps the two matrix factors. -/
theorem complexSecondRowFactorEquiv_theta (X : D) :
    complexSecondRowFactorEquiv D hD (secondRowLieTheta complexJordan complexOperatorAlgebra D hD X) =
      (complexSecondRowFactorEquiv D hD X).swap := by
  obtain ⟨Y, rfl⟩ := (coordOnSpace D hD).symm.surjective X
  obtain ⟨⟨A', x⟩, rfl⟩ := (secondRowCoordinates complexJordan complexOperatorAlgebra).surjective Y
  obtain ⟨A, rfl⟩ := commutatorCoord.surjective A'
  change complexSecondRowFactorEquiv D hD
    (secondRowLieTheta complexJordan complexOperatorAlgebra D hD
      ((LinearEquiv.ofEq _ _ hD.symm)
        (secondRowCoordinates complexJordan complexOperatorAlgebra (commutatorCoord A, x)))) = _
  rw [secondRowLieTheta_onSpace, secondRowTheta_coordinates]
  have he : LinearEquiv.ofEq (secondRowSpace complexJordan complexOperatorAlgebra)
      D.toSubmodule hD.symm = (coordOnSpace D hD).symm := by
    apply LinearEquiv.ext
    intro z
    apply Subtype.ext
    rfl
  rw [he]
  change factorCoordinates ((coordOnSpace D hD) ((coordOnSpace D hD).symm
    (secondRowCoordinates complexJordan complexOperatorAlgebra (commutatorCoord A, -x)))) =
    (factorCoordinates ((coordOnSpace D hD) ((coordOnSpace D hD).symm
      (secondRowCoordinates complexJordan complexOperatorAlgebra (commutatorCoord A, x))))).swap
  simp [factorCoordinates_apply, sub_eq_add_neg]

/-- The factor-exchange clause in the form used by the Killing metric comparison. -/
theorem complexSecondRowFactorEquiv_exchange (A : secondRowCompactSU 3) :
    complexSecondRowFactorEquiv D hD (secondRowLieTheta complexJordan complexOperatorAlgebra D hD
      ((complexSecondRowFactorEquiv D hD).symm (A, 0))) = (0, A) := by
  rw [complexSecondRowFactorEquiv_theta, LieEquiv.apply_symm_apply]
  rfl

end
end ThirteenPlanes.Cartan
