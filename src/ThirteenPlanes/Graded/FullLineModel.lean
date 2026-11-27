module

public import ThirteenPlanes.Graded.LineAlgebras

@[expose] public section

set_option backward.privateInPublic true

/-! Restoring the common trace unit on the line qutrit. -/

namespace ThirteenPlanes.Graded

open scoped Matrix RealInnerProductSpace

noncomputable section

/-- All Hermitian complex three-by-three matrices, with their real vector structure. -/
def fullHermitianSubspace : Submodule ℝ ComplexMatrix3 where
  carrier := {A | A.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' := fun hA hB => hA.add hB
  smul_mem' r _A hA := hA.smul (show IsSelfAdjoint r from star_trivial r)

abbrev FullHermitian3 := ↥fullHermitianSubspace

/-- The full symmetrized matrix product on the Hermitian algebra. -/
def fullHermitianProduct (x y : FullHermitian3) : FullHermitian3 :=
  ⟨symmetricMatrixProduct x.val y.val, symmetricMatrixProduct_hermitian x.property y.property⟩

private theorem matrix_real_smul (r : ℝ) (X : ComplexMatrix3) :
    r • X = (r : ℂ) • X := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

private def matrixJoin (u : TracelessHermitian3 × ℝ) : FullHermitian3 :=
  ⟨TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3),
    u.1.isHermitian.add (Matrix.isHermitian_one.smul (show IsSelfAdjoint u.2 from star_trivial _))⟩

private theorem matrixJoin_trace (u : TracelessHermitian3 × ℝ) :
    Matrix.trace (matrixJoin u).val = 3 * (u.2 : ℂ) := by
  change Matrix.trace (TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3)) = _
  rw [Matrix.trace_add, TracelessHermitian3.trace_eq_zero, matrix_real_smul, Matrix.trace_smul,
    trace_one_matrix3, zero_add, smul_eq_mul, mul_comm]

private def matrixSplitEquiv : (TracelessHermitian3 × ℝ) ≃ₗ[ℝ] FullHermitian3 where
  toFun := matrixJoin
  invFun A := (TracelessHermitian3.ofMatrix (traceFreePart A.val)
    (traceFreePart_hermitian A.property) (trace_traceFreePart _), (Matrix.trace A.val).re / 3)
  left_inv u := by
    apply Prod.ext
    · apply TracelessHermitian3.toMatrix_injective
      rw [TracelessHermitian3.toMatrix_ofMatrix, traceFreePart, matrixJoin_trace]
      change TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3) -
        ((3 * (u.2 : ℂ)) / 3) • (1 : ComplexMatrix3) = _
      rw [matrix_real_smul, show 3 * (u.2 : ℂ) / 3 = u.2 by ring, add_sub_cancel_right]
    · change (Matrix.trace (matrixJoin u).val).re / 3 = u.2
      rw [matrixJoin_trace]
      simp [Complex.mul_re]
  right_inv A := by
    apply Subtype.ext
    change TracelessHermitian3.toMatrix (TracelessHermitian3.ofMatrix (traceFreePart A.val)
      (traceFreePart_hermitian A.property) (trace_traceFreePart _)) +
      ((Matrix.trace A.val).re / 3 : ℝ) • (1 : ComplexMatrix3) = A.val
    rw [TracelessHermitian3.toMatrix_ofMatrix, traceFreePart, matrix_real_smul,
      Complex.ofReal_div, ← hermitian_trace_eq_real A.property]
    norm_num
  map_add' u v := by
    apply Subtype.ext
    change TracelessHermitian3.toMatrix (u.1 + v.1) + (u.2 + v.2) • (1 : ComplexMatrix3) =
      (TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3)) +
      (TracelessHermitian3.toMatrix v.1 + v.2 • (1 : ComplexMatrix3))
    rw [map_add, add_smul]
    abel
  map_smul' r u := by
    apply Subtype.ext
    change TracelessHermitian3.toMatrix (r • u.1) + (r * u.2) • (1 : ComplexMatrix3) =
      r • (TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3))
    rw [map_smul, smul_add, smul_smul]

private def matrixPairProduct (u v : TracelessHermitian3 × ℝ) : TracelessHermitian3 × ℝ :=
  (TracelessHermitian3.jordan u.1 v.1 + u.2 • v.1 + v.2 • u.1,
    ⟪u.1, v.1⟫ / 3 + u.2 * v.2)

private theorem matrixSymProduct_trace (x y : TracelessHermitian3) :
    Matrix.trace (symmetricMatrixProduct (TracelessHermitian3.toMatrix x)
      (TracelessHermitian3.toMatrix y)) = (⟪x,y⟫ : ℝ) := by
  let A := TracelessHermitian3.toMatrix x
  let B := TracelessHermitian3.toMatrix y
  have hp := symmetricMatrixProduct_hermitian x.isHermitian y.isHermitian
  rw [hermitian_trace_eq_real hp, TracelessHermitian3.inner_eq_tracePairing, tracePairing]
  congr 1
  change (Matrix.trace (symmetricMatrixProduct A B)).re = (Matrix.trace (A * B)).re
  have h : Matrix.trace (symmetricMatrixProduct A B) = Matrix.trace (A * B) := by
    simp only [symmetricMatrixProduct, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
    rw [Matrix.trace_mul_comm B A]
    ring
  rw [h]

private theorem matrixSplit_product (u v : TracelessHermitian3 × ℝ) :
    matrixSplitEquiv (matrixPairProduct u v) =
      fullHermitianProduct (matrixSplitEquiv u) (matrixSplitEquiv v) := by
  apply Subtype.ext
  let A := TracelessHermitian3.toMatrix u.1
  let B := TracelessHermitian3.toMatrix v.1
  change TracelessHermitian3.toMatrix (TracelessHermitian3.jordan u.1 v.1 + u.2 • v.1 + v.2 • u.1)
      + (⟪u.1, v.1⟫ / 3 + u.2 * v.2) • (1 : ComplexMatrix3) =
    symmetricMatrixProduct (A + u.2 • (1 : ComplexMatrix3)) (B + v.2 • (1 : ComplexMatrix3))
  have hC : TracelessHermitian3.toMatrix (TracelessHermitian3.jordan u.1 v.1) =
      traceFreePart (symmetricMatrixProduct A B) := rfl
  simp only [map_add, map_smul, hC]
  change traceFreePart (symmetricMatrixProduct A B) + u.2 • B + v.2 • A +
    (⟪u.1, v.1⟫ / 3 + u.2 * v.2) • (1 : ComplexMatrix3) = _
  have ht : Matrix.trace (symmetricMatrixProduct A B) = (⟪u.1, v.1⟫ : ℝ) :=
    matrixSymProduct_trace u.1 v.1
  rw [traceFreePart, ht]
  simp only [matrix_real_smul, symmetricMatrixProduct, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, one_mul, mul_one, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, smul_add, smul_smul, add_smul]
  module

private def nativeLineJoin (l : SignedPlaneIndex) (j : TracelessHermitian3 →ₗᵢ[ℝ] NativeTraceless)
    (hj : LinearMap.range j.toLinearMap = lineTraceless l) :
    (TracelessHermitian3 × ℝ) →ₗ[ℝ] lineAlgebra l where
  toFun u := ⟨(j u.1 : Glennie.Albert) + u.2 • (1 : Glennie.Albert), by
    have hmem : j u.1 ∈ lineTraceless l := hj ▸ ⟨u.1, rfl⟩
    exact (lineAlgebra l).add_mem hmem ((lineAlgebra l).smul_mem _ (lineAlgebra_one l))⟩
  map_add' u v := by
    apply Subtype.ext
    change (j (u.1 + v.1) : Glennie.Albert) + (u.2 + v.2) • (1 : Glennie.Albert) = _
    simp only [map_add, Submodule.coe_add, add_smul]
    abel
  map_smul' r u := by
    apply Subtype.ext
    change (j (r • u.1) : Glennie.Albert) + (r * u.2) • (1 : Glennie.Albert) = _
    simp only [map_smul, Submodule.coe_smul, smul_add, smul_smul, RingHom.id_apply]

private theorem lineJoin_trace (l : SignedPlaneIndex) (j : TracelessHermitian3 →ₗᵢ[ℝ] NativeTraceless)
    (hj : LinearMap.range j.toLinearMap = lineTraceless l) (u : TracelessHermitian3 × ℝ) :
    Glennie.trace (nativeLineJoin l j hj u).val = u.2 * 3 := by
  change Glennie.trace ((j u.1 : Glennie.Albert) + u.2 • (1 : Glennie.Albert)) = _
  simp [Glennie.trace_unit]

private theorem lineJoin_bijective (l : SignedPlaneIndex)
    (j : TracelessHermitian3 →ₗᵢ[ℝ] NativeTraceless)
    (hj : LinearMap.range j.toLinearMap = lineTraceless l) :
    Function.Bijective (nativeLineJoin l j hj) := by
  constructor
  · intro u v he
    have hscalar : u.2 = v.2 := by
      have h := congrArg (fun x : lineAlgebra l => Glennie.trace x.val) he
      simp only [lineJoin_trace] at h
      linarith
    have hx := congrArg Subtype.val he
    change (j u.1 : Glennie.Albert) + u.2 • (1 : Glennie.Albert) =
      (j v.1 : Glennie.Albert) + v.2 • (1 : Glennie.Albert) at hx
    rw [hscalar] at hx
    exact Prod.ext (j.injective (Subtype.ext (add_right_cancel hx))) hscalar
  · intro x
    have hx : (nativeCenter x.val : Glennie.Albert) ∈ lineAlgebra l := by
      rw [nativeCenter_coe, Glennie.traceless]
      exact (lineAlgebra l).sub_mem x.property ((lineAlgebra l).smul_mem _ (lineAlgebra_one l))
    have hy : nativeCenter x.val ∈ LinearMap.range j.toLinearMap := hj.symm ▸ hx
    obtain ⟨y, hy⟩ := hy
    refine ⟨(y, Glennie.trace x.val / 3), Subtype.ext ?_⟩
    change (j y : Glennie.Albert) + (Glennie.trace x.val / 3) • (1 : Glennie.Albert) = x.val
    rw [show j y = nativeCenter x.val from hy, nativeCenter_coe, Glennie.traceless, sub_add_cancel]

private theorem uncentered_of_two_traceless (x y : NativeTraceless) :
    Glennie.jordan x y = (nativeCenteredJordan x y : Glennie.Albert) +
      (⟪x,y⟫ / 3) • (1 : Glennie.Albert) := by
  have hi : ⟪x,y⟫ = Glennie.inner (x : Glennie.Albert) y :=
    Glennie.hilbert_inner_eq_native x y
  rw [hi, nativeCenteredJordan_apply, nativeCenter_coe, Glennie.traceless]
  change _ = Glennie.jordan x y - (Glennie.inner (x : Glennie.Albert) y / 3) •
    (1 : Glennie.Albert) + (Glennie.inner (x : Glennie.Albert) y / 3) • (1 : Glennie.Albert)
  exact (sub_add_cancel _ _).symm

set_option maxHeartbeats 1200000 in
private theorem lineJoin_product (l : SignedPlaneIndex)
    (j : TracelessHermitian3 →ₗᵢ[ℝ] NativeTraceless)
    (hj : LinearMap.range j.toLinearMap = lineTraceless l)
    (hJ : ∀ x y, j (TracelessHermitian3.jordan x y) = nativeCenteredJordan (j x) (j y))
    (u v : TracelessHermitian3 × ℝ) :
    (nativeLineJoin l j hj (matrixPairProduct u v)).val =
      Glennie.jordan (nativeLineJoin l j hj u).val (nativeLineJoin l j hj v).val := by
  change (j (TracelessHermitian3.jordan u.1 v.1 + u.2 • v.1 + v.2 • u.1) : Glennie.Albert) +
    (⟪u.1,v.1⟫ / 3 + u.2 * v.2) • (1 : Glennie.Albert) =
    Glennie.jordan ((j u.1 : Glennie.Albert) + u.2 • (1 : Glennie.Albert))
      ((j v.1 : Glennie.Albert) + v.2 • (1 : Glennie.Albert))
  have hcenter : Glennie.jordan (j u.1) (j v.1) =
      (j (TracelessHermitian3.jordan u.1 v.1) : Glennie.Albert) +
        (⟪u.1,v.1⟫ / 3) • (1 : Glennie.Albert) := by
    calc
      _ = (nativeCenteredJordan (j u.1) (j v.1) : Glennie.Albert) +
          (⟪j u.1, j v.1⟫ / 3) • (1 : Glennie.Albert) :=
        uncentered_of_two_traceless (j u.1) (j v.1)
      _ = _ := by
        have hi : ⟪j u.1, j v.1⟫ = ⟪u.1, v.1⟫ :=
          LinearIsometry.inner_map_map (𝕜 := ℝ) j u.1 v.1
        rw [← hJ u.1 v.1, hi]
  simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, add_smul,
    Glennie.jordan_add_left, Glennie.jordan_add_right, Glennie.jordan_smul_left,
    Glennie.jordan_smul_right, Glennie.jordan_unit_left, Glennie.jordan_unit_right, hcenter]
  module

/-- The full native projective-line algebra is isomorphic to the literal Hermitian complex
three-by-three matrix Jordan algebra. The isomorphism preserves the unit and real trace. -/
theorem nativeLineHermitianModel (l : SignedPlaneIndex) :
    ∃ I : FullHermitian3 ≃ₗ[ℝ] lineAlgebra l,
      (I ⟨1, Matrix.isHermitian_one⟩).val = (1 : Glennie.Albert) ∧
      (∀ X, Glennie.trace (I X).val = (Matrix.trace X.val).re) ∧
      (∀ X Y, (I (fullHermitianProduct X Y)).val = Glennie.jordan (I X).val (I Y).val) := by
  obtain ⟨j, _, hj, _, hJ⟩ := nativeLineTracelessModel l
  let e := LinearEquiv.ofBijective (nativeLineJoin l j hj) (lineJoin_bijective l j hj)
  let I := matrixSplitEquiv.symm.trans e
  refine ⟨I, ?_, ?_, ?_⟩
  · change (e (matrixSplitEquiv.symm ⟨1, Matrix.isHermitian_one⟩)).val = _
    have he : matrixSplitEquiv (0, 1) = ⟨1, Matrix.isHermitian_one⟩ := by
      apply Subtype.ext
      change TracelessHermitian3.toMatrix 0 + (1 : ℝ) • (1 : ComplexMatrix3) = 1
      simp
    rw [← he, LinearEquiv.symm_apply_apply]
    change (j 0 : Glennie.Albert) + (1 : ℝ) • (1 : Glennie.Albert) = 1
    simp
  · intro X
    obtain ⟨u, rfl⟩ := matrixSplitEquiv.surjective X
    change Glennie.trace (e (matrixSplitEquiv.symm (matrixSplitEquiv u))).val = _
    rw [LinearEquiv.symm_apply_apply]
    change Glennie.trace (nativeLineJoin l j hj u).val = (Matrix.trace (matrixJoin u).val).re
    rw [lineJoin_trace, matrixJoin_trace]
    simp [Complex.mul_re, mul_comm]
  · intro X Y
    obtain ⟨u, rfl⟩ := matrixSplitEquiv.surjective X
    obtain ⟨v, rfl⟩ := matrixSplitEquiv.surjective Y
    rw [← matrixSplit_product]
    simp only [I, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact lineJoin_product l j hj hJ u v

end

end ThirteenPlanes.Graded
