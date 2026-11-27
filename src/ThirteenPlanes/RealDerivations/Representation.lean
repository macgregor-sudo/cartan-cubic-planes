module

public import ThirteenPlanes.RealDerivations.TraceBridge
public import ThirteenPlanes.RealDerivations.Characteristic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Zero

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RealDerivations

open Peirce Polynomial Module
open scoped Matrix RealInnerProductSpace

noncomputable section

def traceCoord (x : V) : Fin 5 → ℝ :=
  let X := realTraceMatrix x
  ![X 0 0, X 1 1, X 0 1, X 0 2, X 1 2]

private def traceCoordLinear : V →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun := traceCoord
  map_add' x y := by
    have h := realTraceLinear.map_add x y
    change realTraceMatrix (x + y) = _ at h
    funext i
    fin_cases i <;> simp [traceCoord, h, realTraceLinear]
  map_smul' r x := by
    have h := realTraceLinear.map_smul r x
    change realTraceMatrix (r • x) = _ at h
    funext i
    fin_cases i <;> simp [traceCoord, h, realTraceLinear]

def traceChart (v : Fin 5 → ℝ) : M₃ :=
  !![v 0, v 2, v 3; v 2, v 1, v 4; v 3, v 4, -v 0 - v 1]

theorem traceChart_coord (x : V) : traceChart (traceCoord x) = realTraceMatrix x := by
  have hd : Matrix.trace (realTraceMatrix x) = 0 := traceMatrix_trace x
  have hs (i j : Fin 3) : realTraceMatrix x j i = realTraceMatrix x i j := symm (traceMatrix x) i j
  have h22 : realTraceMatrix x 2 2 = -realTraceMatrix x 0 0 - realTraceMatrix x 1 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three] at hd
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceChart, traceCoord, hs 0 1, hs 0 2, hs 1 2, h22]

def traceCoordEquiv : V ≃ₗ[ℝ] (Fin 5 → ℝ) :=
  LinearEquiv.ofBijective traceCoordLinear ⟨by
    intro x y hxy
    have hm : realTraceMatrix x = realTraceMatrix y := by
      rw [← traceChart_coord x, ← traceChart_coord y]
      exact congrArg traceChart hxy
    exact traceMatrixEquiv.injective (Subtype.ext (Subtype.ext hm)), by
    intro v
    have hs : (traceChart v)ᵀ = traceChart v := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have htr : Matrix.trace (traceChart v) = 0 := by
      simp [Matrix.trace, traceChart, Fin.sum_univ_three]
    obtain ⟨x, hx⟩ := (realTraceMatrix_range _).mpr ⟨hs, htr⟩
    refine ⟨x, ?_⟩
    change traceCoord x = v
    funext i
    fin_cases i <;> simp [traceCoord, hx, traceChart]⟩

def coordBasis : Basis (Fin 5) ℝ V := Basis.ofEquivFun traceCoordEquiv

private theorem skew_normal {T : M₃} (hT : Tᵀ = -T) :
    T = !![0, -(T 1 0), -(T 2 0); T 1 0, 0, -(T 2 1); T 2 0, T 2 1, 0] := by
  have ht (i j : Fin 3) : T j i = -T i j := congrArg (fun A : M₃ => A i j) hT
  have hz (i : Fin 3) : T i i = 0 := by linarith only [ht i i]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact hz _ | exact ht _ _

private theorem actual_commutator_coord {D : Module.End ℝ V} {T : M₃} (hT : Tᵀ = -T)
    (hD : ∀ x : V, realTraceMatrix (D x) = T * realTraceMatrix x - realTraceMatrix x * T)
    (x : V) : traceCoord (D x) = (commutatorMatrix (T 1 0) (T 2 0) (T 2 1)).mulVec (traceCoord x) := by
  let a := T 1 0
  let b := T 2 0
  let c := T 2 1
  have ht : T = !![0, -a, -b; a, 0, -c; b, c, 0] := skew_normal hT
  have he := hD x
  rw [ht, ← traceChart_coord x] at he
  change traceCoord (D x) = (commutatorMatrix a b c).mulVec (traceCoord x)
  funext i
  fin_cases i <;>
    norm_num [traceCoord, he, Matrix.mul_apply, traceChart, Matrix.mulVec, dotProduct,
      commutatorMatrix, Fin.sum_univ_succ] <;> ring

private theorem actual_commutator_matrix {D : Module.End ℝ V} {T : M₃} (hT : Tᵀ = -T)
    (hD : ∀ x : V, realTraceMatrix (D x) = T * realTraceMatrix x - realTraceMatrix x * T) :
    LinearMap.toMatrix coordBasis coordBasis D = commutatorMatrix (T 1 0) (T 2 0) (T 2 1) := by
  ext i j
  rw [LinearMap.toMatrix_apply, coordBasis, Basis.ofEquivFun_repr_apply]
  change traceCoord (D (coordBasis j)) i = _
  rw [actual_commutator_coord hT hD]
  have hv : traceCoord (coordBasis j) = Pi.single j 1 := by
    funext k
    change traceCoordEquiv (coordBasis j) k = _
    calc
      _ = (coordBasis.repr (coordBasis j)) k :=
        (Basis.ofEquivFun_repr_apply traceCoordEquiv (coordBasis j) k).symm
      _ = _ := by rw [Basis.repr_self, Finsupp.single_eq_pi_single]
  rw [hv]
  simp [Matrix.col_apply]

def traceAdjoint (D : Module.End ℝ V) : Module.End ℝ V :=
  LinearMap.adjoint (𝕜 := ℝ) (E := RealTracelessSymmetric3) (F := RealTracelessSymmetric3) D

private theorem adjoint_of_skew {D : Module.End ℝ V} (hs : ∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫) :
    traceAdjoint D = -D := by
  ext x : 1
  apply ext_inner_left ℝ
  intro y
  rw [traceAdjoint, LinearMap.adjoint_inner_right]
  change ⟪D y, x⟫ = ⟪y, -(D x)⟫
  exact (hs y x).trans (inner_neg_right y (D x)).symm

/-- The actual Gram operator of the skew commutator has five characteristic roots, with
multiplicity. With q = a² + b² + c² these are 0, q, q, 4q, 4q. -/
theorem actual_commutatorGram_charpoly {D : Module.End ℝ V} {T : M₃} (hT : Tᵀ = -T)
    (hD : ∀ x : V, realTraceMatrix (D x) = T * realTraceMatrix x - realTraceMatrix x * T)
    (hs : ∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫) :
    let q := (T 1 0) ^ 2 + (T 2 0) ^ 2 + (T 2 1) ^ 2
    ((traceAdjoint D).comp D).charpoly = X * (X - C q) ^ 2 * (X - C (4 * q)) ^ 2 := by
  dsimp only
  have ha : (traceAdjoint D).comp D = -(D.comp D) := by
    rw [adjoint_of_skew hs]
    rfl
  let A := commutatorMatrix (T 1 0) (T 2 0) (T 2 1)
  have hA : LinearMap.toMatrix coordBasis coordBasis D = A := actual_commutator_matrix hT hD
  let M : Module.End ℝ V ≃ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℝ :=
    LinearMap.toMatrix coordBasis coordBasis
  have hneg : M (-D) = -A := (map_neg M D).trans (congrArg Neg.neg hA)
  have hM : M ((traceAdjoint D).comp D) = -(A * A) := by
    calc
      _ = M ((-D).comp D) := congrArg M ha
      _ = M (-D) * M D := LinearMap.toMatrix_comp coordBasis coordBasis coordBasis (-D) D
      _ = (-A) * A := congrArg₂ (· * ·) hneg hA
      _ = _ := neg_mul _ _
  calc
    _ = (LinearMap.toMatrix coordBasis coordBasis ((traceAdjoint D).comp D)).charpoly :=
      (LinearMap.charpoly_toMatrix _ coordBasis).symm
    _ = (-(A * A)).charpoly := congrArg Matrix.charpoly hM
    _ = _ := commutatorGram_charpoly _ _ _

/-- The literal matrix commutator acts on the actual traceless carrier. -/
def tracelessCommutator (T : M₃) (hT : Tᵀ = -T) : Module.End ℝ V :=
  readTraceZero.comp ((commutator T hT).comp traceMatrixLinear)

theorem tracelessCommutator_matrix (T : M₃) (hT : Tᵀ = -T) (x : V) :
    realTraceMatrix (tracelessCommutator T hT x) = T * realTraceMatrix x - realTraceMatrix x * T := by
  change (traceMatrix (readTraceZero (commutator T hT (traceMatrix x)))).val = _
  rw [traceMatrix_readTraceZero, centerLinear_apply]
  have ht : trace (commutator T hT (traceMatrix x)) = 0 := by
    rw [trace_apply, commutator_apply, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [ht, zero_div, zero_smul, sub_zero, commutator_apply]
  rfl

theorem tracelessCommutator_skew (T : M₃) (hT : Tᵀ = -T) (x y : V) :
    ⟪tracelessCommutator T hT x, y⟫ = -⟪x, tracelessCommutator T hT y⟫ := by
  rw [realTraceMatrix_inner, realTraceMatrix_inner, tracelessCommutator_matrix,
    tracelessCommutator_matrix, sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_sub]
  have hcyc := (Matrix.trace_mul_cycle T (realTraceMatrix x) (realTraceMatrix y)).trans
    (Matrix.trace_mul_cycle (realTraceMatrix y) T (realTraceMatrix x))
  rw [hcyc, ← mul_assoc (realTraceMatrix x) T (realTraceMatrix y),
    ← mul_assoc (realTraceMatrix x) (realTraceMatrix y) T]
  ring

/-- For a nonzero real skew matrix, the Gram roots on the actual traceless matrices
are the squares of 0, λ, λ, 2λ, and 2λ, with λ positive. -/
theorem tracelessCommutator_singular_spectrum (T : M₃) (hT : Tᵀ = -T) (hne : T ≠ 0) :
    ∃ s : ℝ, 0 < s ∧
      ((traceAdjoint (tracelessCommutator T hT)).comp (tracelessCommutator T hT)).charpoly =
        X * (X - C (s ^ 2)) ^ 2 * (X - C ((2 * s) ^ 2)) ^ 2 := by
  let q := (T 1 0) ^ 2 + (T 2 0) ^ 2 + (T 2 1) ^ 2
  have hq : 0 < q := by
    by_contra! h
    have ha : T 1 0 = 0 := by dsimp [q] at h; nlinarith
    have hb : T 2 0 = 0 := by dsimp [q] at h; nlinarith
    have hc : T 2 1 = 0 := by dsimp [q] at h; nlinarith
    apply hne
    rw [skew_normal hT, ha, hb, hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨Real.sqrt q, Real.sqrt_pos.mpr hq, ?_⟩
  have hG := actual_commutatorGram_charpoly hT (tracelessCommutator_matrix T hT)
    (tracelessCommutator_skew T hT)
  have hv : (2 * Real.sqrt q) ^ 2 = 4 * q := by
    rw [mul_pow, Real.sq_sqrt hq.le]
    norm_num
  rw [Real.sq_sqrt hq.le, hv]
  exact hG

end
end ThirteenPlanes.RealDerivations
