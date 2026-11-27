/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.FourPlanesProjectors
public import ThirteenPlanes.Matrix3Jordan

/-! The planes of trace-free matrices diagonal in the four qutrit bases. -/

@[expose] public section
noncomputable section

namespace ThirteenPlanes

open scoped ComplexOrder
open AlbertSequential
open TracelessHermitian3

/-- Form a matrix with real diagonal entries in the given qutrit basis. -/
def matrixFrameSynthesis (k : Fin 4) : (Fin 3 → ℝ) →ₗ[ℝ] ComplexMatrix3 where
  toFun u := ∑ b, u b • qutritMUBProjection k b
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum, mul_smul]

@[simp] theorem trace_matrixFrameSynthesis (k : Fin 4) (u : Fin 3 → ℝ) :
    Matrix.trace (matrixFrameSynthesis k u) = ((∑ b, u b : ℝ) : ℂ) := by
  change Matrix.trace (∑ b, u b • qutritMUBProjection k b) = _
  simp [Complex.real_smul, qutritMUBProjection_trace]

theorem matrixFrameSynthesis_hermitian (k : Fin 4) (u : Fin 3 → ℝ) :
    (matrixFrameSynthesis k u).IsHermitian := by
  change (∑ b, u b • qutritMUBProjection k b).IsHermitian
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
  apply Finset.sum_congr rfl
  intro b _
  rw [(qutritMUBProjection_positive k b).isHermitian.eq]

@[simp] theorem matrixFrameSynthesis_const (k : Fin 4) (r : ℝ) :
    matrixFrameSynthesis k (fun _ => r) = r • (1 : ComplexMatrix3) := by
  change (∑ b, r • qutritMUBProjection k b) = _
  rw [← Finset.smul_sum, qutritMUBProjection_sum]

theorem qutritProjection_mul_own_basis (k : Fin 4) (b c : Fin 3) :
    qutritMUBProjection k b * qutritMUBProjection k c =
      if b = c then qutritMUBProjection k b else 0 := by
  by_cases h : b = c
  · subst c
    simpa using qutritMUBProjection_idempotent k b
  · rw [ite_eq_right h]
    ext i j
    change (qutritRankOneProjection (qutritBasisVector k b) *
      qutritRankOneProjection (qutritBasisVector k c)) i j = 0
    rw [qutritRankOneProjection_mul_apply, qutritBasisVector_orthonormal, ite_eq_right h, mul_zero,
      zero_mul]

theorem matrixFrameSynthesis_mul (k : Fin 4) (u v : Fin 3 → ℝ) :
    matrixFrameSynthesis k u * matrixFrameSynthesis k v =
      matrixFrameSynthesis k (fun b => u b * v b) := by
  change (∑ b, u b • qutritMUBProjection k b) * (∑ b, v b • qutritMUBProjection k b) =
    ∑ b, (u b * v b) • qutritMUBProjection k b
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, qutritProjection_mul_own_basis]
  rw [Finset.sum_eq_single b]
  · simp [smul_smul, mul_comm]
  · intro c _ h
    simp [Ne.symm h]
  · simp

theorem traceFreePart_matrixFrameSynthesis (k : Fin 4) (u : Fin 3 → ℝ) :
    traceFreePart (matrixFrameSynthesis k u) =
      matrixFrameSynthesis k (fun b => u b - (∑ c, u c) / 3) := by
  show traceFreePart (matrixFrameSynthesis k u) =
    matrixFrameSynthesis k (u - (fun _ => (∑ c, u c) / 3))
  rw [map_sub, matrixFrameSynthesis_const, traceFreePart, trace_matrixFrameSynthesis]
  congr 1
  change (((∑ b, u b : ℝ) : ℂ) / 3) • (1 : ComplexMatrix3) =
    ((((∑ b, u b) / 3 : ℝ) : ℂ)) • (1 : ComplexMatrix3)
  push_cast
  rfl

def matrixFrameAnalysis (k : Fin 4) (X : ComplexMatrix3) (b : Fin 3) : ℝ :=
  tracePairing (qutritMUBProjection k b) X

theorem matrixFrameAnalysis_add (k : Fin 4) (X Y : ComplexMatrix3) :
    matrixFrameAnalysis k (X + Y) = matrixFrameAnalysis k X + matrixFrameAnalysis k Y := by
  funext b
  simp [matrixFrameAnalysis, tracePairing, mul_add]

theorem matrixFrameAnalysis_smul (k : Fin 4) (r : ℝ) (X : ComplexMatrix3) :
    matrixFrameAnalysis k (r • X) = r • matrixFrameAnalysis k X := by
  funext b
  simp [matrixFrameAnalysis, tracePairing]

theorem sum_matrixFrameAnalysis (k : Fin 4) (X : ComplexMatrix3) :
    ∑ b, matrixFrameAnalysis k X b = (Matrix.trace X).re := by
  change ∑ b, Complex.reAddGroupHom (Matrix.trace (qutritMUBProjection k b * X)) =
    Complex.reAddGroupHom (Matrix.trace X)
  rw [← map_sum, ← Matrix.trace_sum, ← Finset.sum_mul, qutritMUBProjection_sum, one_mul]

theorem matrixFrameAnalysis_synthesis (k l : Fin 4) (u : Fin 3 → ℝ) (b : Fin 3) :
    matrixFrameAnalysis k (matrixFrameSynthesis l u) b =
      if k = l then u b else (∑ c, u c) / 3 := by
  change Complex.reAddGroupHom
    (Matrix.trace (qutritMUBProjection k b * ∑ c, u c • qutritMUBProjection l c)) = _
  rw [Finset.mul_sum, Matrix.trace_sum, map_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, qutritProjection_pairTrace]
  change (∑ c, (u c • (if k = l then (if b = c then 1 else 0) else (1 / 3 : ℂ))).re) = _
  simp only [Complex.smul_re]
  by_cases h : k = l
  · simp [h, apply_ite]
  · norm_num [h, Complex.div_re]
    calc
      _ = (∑ c, u c) * 3⁻¹ := by simp only [Finset.sum_mul, one_div]
      _ = _ := (div_eq_mul_inv _ _).symm

/-- Orthogonal projection onto the plane of trace-free diagonals in one basis. -/
def matrixFrameProjectionValue (k : Fin 4) (x : TracelessHermitian3) :
    TracelessHermitian3 :=
  ofMatrix (matrixFrameSynthesis k (matrixFrameAnalysis k (toMatrix x)))
    (matrixFrameSynthesis_hermitian _ _)
    (by rw [trace_matrixFrameSynthesis, sum_matrixFrameAnalysis, trace_eq_zero, Complex.zero_re,
      Complex.ofReal_zero])

def matrixFrameProjection (k : Fin 4) : TracelessHermitian3 →ₗ[ℝ] TracelessHermitian3 where
  toFun := matrixFrameProjectionValue k
  map_add' x y := by
    apply toMatrix_injective
    simp only [matrixFrameProjectionValue, toMatrix_ofMatrix, map_add, matrixFrameAnalysis_add]
  map_smul' r x := by
    apply toMatrix_injective
    simp only [matrixFrameProjectionValue, toMatrix_ofMatrix, map_smul, matrixFrameAnalysis_smul,
      RingHom.id_apply]

@[simp] theorem toMatrix_matrixFrameProjection (k : Fin 4) (x : TracelessHermitian3) :
    toMatrix (matrixFrameProjection k x) = matrixFrameSynthesis k (matrixFrameAnalysis k (toMatrix x)) :=
  rfl

theorem matrixFrameProjection_synthesis (k : Fin 4) (u : Fin 3 → ℝ)
    (h : ∑ b, u b = 0) :
    matrixFrameProjection k (ofMatrix (matrixFrameSynthesis k u)
      (matrixFrameSynthesis_hermitian k u) (by simp [h])) =
    ofMatrix (matrixFrameSynthesis k u) (matrixFrameSynthesis_hermitian k u) (by simp [h]) := by
  apply toMatrix_injective
  simp only [toMatrix_matrixFrameProjection, toMatrix_ofMatrix]
  congr 1
  funext b
  simp [matrixFrameAnalysis_synthesis]

theorem matrixFrameProjection_comp (k l : Fin 4) (x : TracelessHermitian3) :
    matrixFrameProjection k (matrixFrameProjection l x) =
      if k = l then matrixFrameProjection l x else 0 := by
  apply toMatrix_injective
  by_cases h : k = l
  · simp only [h, ↓reduceIte, toMatrix_matrixFrameProjection]
    congr 1
    funext b
    simp [matrixFrameAnalysis_synthesis]
  · simp only [h, ↓reduceIte, toMatrix_matrixFrameProjection, map_zero]
    have hcoeff : matrixFrameAnalysis k (matrixFrameSynthesis l
        (matrixFrameAnalysis l (toMatrix x))) = 0 := by
      funext b
      simp [matrixFrameAnalysis_synthesis, h, sum_matrixFrameAnalysis]
    rw [hcoeff, map_zero]

theorem tracePairing_synthesis_left (k : Fin 4) (u : Fin 3 → ℝ) (X : ComplexMatrix3) :
    tracePairing (matrixFrameSynthesis k u) X = ∑ b, u b * matrixFrameAnalysis k X b := by
  change Complex.reAddGroupHom (Matrix.trace ((∑ b, u b • qutritMUBProjection k b) * X)) = _
  rw [Finset.sum_mul, Matrix.trace_sum, map_sum]
  simp [matrixFrameAnalysis, tracePairing]

theorem inner_matrixFrameProjection (k : Fin 4) (x y : TracelessHermitian3) :
    inner ℝ (matrixFrameProjection k x) y =
      ∑ b, matrixFrameAnalysis k (toMatrix x) b * matrixFrameAnalysis k (toMatrix y) b := by
  rw [inner_eq_tracePairing, toMatrix_matrixFrameProjection, tracePairing_synthesis_left]

theorem matrixFrameProjection_inner_swap (k : Fin 4) (x y : TracelessHermitian3) :
    inner ℝ (matrixFrameProjection k x) y = inner ℝ x (matrixFrameProjection k y) := by
  rw [real_inner_comm (matrixFrameProjection k y) x, inner_matrixFrameProjection,
    inner_matrixFrameProjection]
  simp only [mul_comm]

theorem toMatrix_jordan_matrixFrameProjection (k : Fin 4) (x y : TracelessHermitian3) :
    toMatrix (jordan (matrixFrameProjection k x) (matrixFrameProjection k y)) =
      matrixFrameSynthesis k (fun b =>
        matrixFrameAnalysis k (toMatrix x) b * matrixFrameAnalysis k (toMatrix y) b -
          (∑ c, matrixFrameAnalysis k (toMatrix x) c * matrixFrameAnalysis k (toMatrix y) c) / 3) := by
  rw [toMatrix_jordan, toMatrix_matrixFrameProjection, toMatrix_matrixFrameProjection]
  rw [symmetricMatrixProduct, matrixFrameSynthesis_mul, matrixFrameSynthesis_mul]
  simp_rw [mul_comm (matrixFrameAnalysis k (toMatrix y) _) (matrixFrameAnalysis k (toMatrix x) _)]
  rw [← two_smul ℂ, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul,
    traceFreePart_matrixFrameSynthesis]

theorem project_jordan_of_fixed (k : Fin 4) (x y : TracelessHermitian3)
    (hx : matrixFrameProjection k x = x) (hy : matrixFrameProjection k y = y) :
    matrixFrameProjection k (jordan x y) = jordan x y := by
  have hmat := toMatrix_jordan_matrixFrameProjection k x y
  rw [hx, hy] at hmat
  apply toMatrix_injective
  rw [toMatrix_matrixFrameProjection, hmat]
  congr 1
  funext b
  simp [matrixFrameAnalysis_synthesis]

end ThirteenPlanes
