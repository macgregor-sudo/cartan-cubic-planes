module

public import ThirteenPlanes.Quaternionic.FramePlaneSquares
public import ThirteenPlanes.Quaternionic.PairProducts
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

@[expose] public section

/-!
# Matrix-valued square sums on the genuine traceless Hilbert space

The canonical covariant tensor supplies basis independence of a bilinear square
sum. Native coordinate evaluation will use two diagonal vectors and three
quaternion slots, each with its full four-dimensional real orthonormal basis.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

def nativeTracelessMatrix : TracelessHilbert →ₗ[ℝ] QMat :=
  matrixHilbertEquiv.toLinearMap.comp tracelessHilbertSubmodule.subtype

@[simp] lemma nativeTracelessMatrix_apply (v : TracelessHilbert) :
    nativeTracelessMatrix v = matrixHilbertEquiv v.val := rfl

def tracelessOfMatrix (A : QMat) (hA : A.IsHermitian) (ht : rtrace A = 0) : TracelessHilbert :=
  tracelessHilbertEquiv.symm ⟨A, ⟨hA, ht⟩⟩

lemma nativeTracelessMatrix_ofMatrix (A : QMat) (hA : A.IsHermitian) (ht : rtrace A = 0) :
    nativeTracelessMatrix (tracelessOfMatrix A hA ht) = A := by
  exact congrArg Subtype.val (tracelessHilbertEquiv.apply_symm_apply ⟨A, ⟨hA, ht⟩⟩)

lemma nativeTracelessMatrix_inner (v w : TracelessHilbert) :
    inner ℝ v w = traceForm (nativeTracelessMatrix v) (nativeTracelessMatrix w) :=
  tracelessHilbert_inner v w

def nativeProductBilin : TracelessHilbert →ₗ[ℝ] TracelessHilbert →ₗ[ℝ] QMat where
  toFun x :=
    { toFun y := nativeTracelessMatrix x * nativeTracelessMatrix y
      map_add' y z := by simp only [map_add, mul_add]
      map_smul' r y := by simp only [map_smul, mul_smul_comm, RingHom.id_apply] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change nativeTracelessMatrix (x + y) * nativeTracelessMatrix z =
      nativeTracelessMatrix x * nativeTracelessMatrix z + nativeTracelessMatrix y * nativeTracelessMatrix z
    rw [map_add, add_mul]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change nativeTracelessMatrix (r • x) * nativeTracelessMatrix y =
      r • (nativeTracelessMatrix x * nativeTracelessMatrix y)
    rw [map_smul, smul_mul_assoc]

@[simp] lemma nativeProductBilin_apply (x y : TracelessHilbert) :
    nativeProductBilin x y = nativeTracelessMatrix x * nativeTracelessMatrix y := rfl

/-- The sum of native matrix squares is independent of a real orthonormal basis.
This is a standard canonical-tensor consequence, with no inner product assumed
on the matrix-valued codomain and no diagonalization premise. -/
lemma native_square_sum_basis_invariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℝ TracelessHilbert) (f : OrthonormalBasis κ ℝ TracelessHilbert) :
    (∑ i, nativeTracelessMatrix (e i) ^ 2) = ∑ j, nativeTracelessMatrix (f j) ^ 2 := by
  have h := (InnerProductSpace.canonicalCovariantTensor_eq_sum TracelessHilbert e).symm.trans
    (InnerProductSpace.canonicalCovariantTensor_eq_sum TracelessHilbert f)
  have hh := congrArg (TensorProduct.lift nativeProductBilin) h
  simpa only [map_sum, TensorProduct.lift.tmul, nativeProductBilin_apply, pow_two] using hh

lemma rtrace_hermCoordinates (d : Outcome → ℝ) (q : Outcome → Q) :
    rtrace (matrixOfHermCoordinates d q) = ∑ i, d i := by
  simp [rtrace, matrixOfHermCoordinates, Fin.sum_univ_three]

lemma traceForm_hermCoordinates (d e : Outcome → ℝ) (q r : Outcome → Q) :
    traceForm (matrixOfHermCoordinates d q) (matrixOfHermCoordinates e r) =
      (∑ i, d i * e i) + 2 * ∑ i, inner ℝ (q i) (r i) := by
  rw [traceForm_eq_rtrace_mul]
  simp only [rtrace, Matrix.mul_apply]
  norm_num [matrixOfHermCoordinates,
    Matrix.mul_apply, Fin.sum_univ_three, Quaternion.inner_def, Quaternion.re_mul]
  ring

def quaternionOrtho : OrthonormalBasis (Fin 4) ℝ Q := by
  have h : Module.finrank ℝ Q = 4 := Quaternion.finrank_eq_four
  exact (stdOrthonormalBasis ℝ Q).reindex (finCongr h)

def offSlotMatrix (a : Outcome) (q : Q) : QMat :=
  matrixOfHermCoordinates 0 (Pi.single a q)

lemma offSlotMatrix_isHermitian (a : Outcome) (q : Q) :
    (offSlotMatrix a q).IsHermitian := matrixOfHermCoordinates_isHermitian _ _

lemma offSlotMatrix_rtrace (a : Outcome) (q : Q) : rtrace (offSlotMatrix a q) = 0 := by
  rw [offSlotMatrix, rtrace_hermCoordinates]
  simp

lemma traceForm_offSlotMatrix (a b : Outcome) (q r : Q) :
    traceForm (offSlotMatrix a q) (offSlotMatrix b r) =
      if a = b then 2 * inner ℝ q r else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [offSlotMatrix, traceForm_hermCoordinates, Fin.sum_univ_three]

def slotDiagonal (a : Outcome) : QMat :=
  realDiagonal (if a = 0 then ![1, 1, 0] else if a = 1 then ![1, 0, 1] else ![0, 1, 1])

lemma offSlotMatrix_square (a : Outcome) (q : Q) :
    offSlotMatrix a q ^ 2 = Quaternion.normSq q • slotDiagonal a := by
  rw [pow_two]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply]
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [offSlotMatrix, matrixOfHermCoordinates, slotDiagonal, realDiagonal,
      Fin.sum_univ_three, Quaternion.self_mul_star, Quaternion.star_mul_self, Quaternion.smul_coe]
  all_goals rw [← Quaternion.coe_mul_eq_smul, mul_one]

lemma realDiagonal_eq_hermCoordinates (d : Outcome → ℝ) :
    realDiagonal d = matrixOfHermCoordinates d 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [realDiagonal, matrixOfHermCoordinates]

lemma traceForm_realDiagonal_offSlot (d : Outcome → ℝ) (a : Outcome) (q : Q) :
    traceForm (realDiagonal d) (offSlotMatrix a q) = 0 := by
  rw [realDiagonal_eq_hermCoordinates, offSlotMatrix, traceForm_hermCoordinates]
  simp

lemma coordinate_point_realDiagonal (a : Outcome) :
    QBasis.coordinate.point a = realDiagonal (fun i => if i = a then 1 else 0) := by
  apply Matrix.ext
  intro i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [QBasis.point, QBasis.column, QBasis.coordinate, projector,
      Matrix.one_apply, realDiagonal]

lemma coordinate_centered_offSlot (i a : Outcome) (q : Q) :
    traceForm (QBasis.coordinate.toFrame.centeredPointMatrix i) (offSlotMatrix a q) = 0 := by
  rw [Frame.centeredPointMatrix, traceForm_sub_left, traceForm_smul_left,
    traceForm_one_left, offSlotMatrix_rtrace, mul_zero, sub_zero]
  change traceForm (QBasis.coordinate.point i) (offSlotMatrix a q) = 0
  rw [coordinate_point_realDiagonal, traceForm_realDiagonal_offSlot]

def offSlotVector (a : Outcome) (k : Fin 4) : TracelessHilbert :=
  (Real.sqrt 2 / 2 : ℝ) • tracelessOfMatrix (offSlotMatrix a (quaternionOrtho k))
    (offSlotMatrix_isHermitian _ _) (offSlotMatrix_rtrace _ _)

lemma native_offSlotVector (a : Outcome) (k : Fin 4) :
    nativeTracelessMatrix (offSlotVector a k) =
      (Real.sqrt 2 / 2 : ℝ) • offSlotMatrix a (quaternionOrtho k) := by
  rw [offSlotVector, map_smul, nativeTracelessMatrix_ofMatrix]

lemma offSlotVector_gram (a b : Outcome) (k l : Fin 4) :
    inner ℝ (offSlotVector a k) (offSlotVector b l) = if (a,k) = (b,l) then 1 else 0 := by
  have hs : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [nativeTracelessMatrix_inner, native_offSlotVector, native_offSlotVector,
    traceForm_smul_left, traceForm_smul_right, traceForm_offSlotMatrix,
    quaternionOrtho.inner_eq_ite]
  by_cases hab : a = b <;> by_cases hkl : k = l <;> simp [hab, hkl, Prod.mk.injEq]
  nlinarith [hs]

lemma coordinate_plane_offSlot (i : Fin 2) (a : Outcome) (k : Fin 4) :
    inner ℝ (QBasis.coordinate.toFrame.planeOrtho i) (offSlotVector a k) = 0 := by
  rw [nativeTracelessMatrix_inner, native_offSlotVector, traceForm_smul_right]
  fin_cases i
  · change (Real.sqrt 2 / 2) * traceForm
      (matrixHilbertEquiv (QBasis.coordinate.toFrame.planeOrtho 0).val)
      (offSlotMatrix a (quaternionOrtho k)) = 0
    rw [Frame.planeOrtho_matrix_zero, traceForm_smul_left, coordinate_centered_offSlot]
    ring
  · change (Real.sqrt 2 / 2) * traceForm
      (matrixHilbertEquiv (QBasis.coordinate.toFrame.planeOrtho 1).val)
      (offSlotMatrix a (quaternionOrtho k)) = 0
    rw [Frame.planeOrtho_matrix_one, traceForm_smul_left, traceForm_add_left,
      traceForm_smul_left, coordinate_centered_offSlot, coordinate_centered_offSlot]
    ring

abbrev SquareBasisIndex := Fin 2 ⊕ (Outcome × Fin 4)

def canonicalTracelessFamily : SquareBasisIndex → TracelessHilbert :=
  Sum.elim QBasis.coordinate.toFrame.planeOrtho (fun ak => offSlotVector ak.1 ak.2)

lemma canonicalTracelessFamily_orthonormal : Orthonormal ℝ canonicalTracelessFamily := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [canonicalTracelessFamily] using QBasis.coordinate.toFrame.planeOrtho_gram i j
    | inr ak => simpa [canonicalTracelessFamily] using coordinate_plane_offSlot i ak.1 ak.2
  | inr ak =>
    cases j with
    | inl j =>
      simpa [canonicalTracelessFamily, real_inner_comm] using coordinate_plane_offSlot j ak.1 ak.2
    | inr bk => simpa [canonicalTracelessFamily] using offSlotVector_gram ak.1 bk.1 ak.2 bk.2

def canonicalTracelessBasis : OrthonormalBasis SquareBasisIndex ℝ TracelessHilbert :=
  OrthonormalBasis.mk canonicalTracelessFamily_orthonormal
    (canonicalTracelessFamily_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [SquareBasisIndex, finrank_TracelessHilbert])).ge

lemma offSlotVector_square (a : Outcome) (k : Fin 4) :
    nativeTracelessMatrix (offSlotVector a k) ^ 2 = (1 / 2 : ℝ) • slotDiagonal a := by
  have hq : Quaternion.normSq (quaternionOrtho k) = 1 := by
    rw [← Quaternion.inner_self]
    exact quaternionOrtho.inner_eq_one k
  have hs : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [native_offSlotVector, real_smul_square, hs, offSlotMatrix_square, hq, one_smul]

lemma sum_slotDiagonal : (∑ a, slotDiagonal a) = (2 : ℝ) • (1 : QMat) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_three, slotDiagonal, realDiagonal]
  all_goals rw [← Quaternion.coe_mul_eq_smul, mul_one]; rfl

lemma offSlotVector_square_sum :
    (∑ ak : Outcome × Fin 4, nativeTracelessMatrix (offSlotVector ak.1 ak.2) ^ 2) =
      (4 : ℝ) • (1 : QMat) := by
  rw [Fintype.sum_prod_type]
  have h (a : Outcome) :
      (∑ k : Fin 4, nativeTracelessMatrix (offSlotVector a k) ^ 2) = (2 : ℝ) • slotDiagonal a := by
    simp only [offSlotVector_square, Fin.sum_univ_four]
    module
  simp only [h]
  rw [← Finset.smul_sum, sum_slotDiagonal, smul_smul]
  norm_num

lemma canonicalTracelessBasis_square_sum :
    (∑ i, nativeTracelessMatrix (canonicalTracelessBasis i) ^ 2) =
      (14 / 3 : ℝ) • (1 : QMat) := by
  have hd : (∑ i : Fin 2, nativeTracelessMatrix (QBasis.coordinate.toFrame.planeOrtho i) ^ 2) =
      (2 / 3 : ℝ) • (1 : QMat) := by
    simpa only [Fin.sum_univ_two, nativeTracelessMatrix_apply] using QBasis.coordinate.toFrame.planeOrtho_square_sum
  simp only [canonicalTracelessBasis, OrthonormalBasis.coe_mk, Fintype.sum_sum_type,
    canonicalTracelessFamily, Sum.elim_inl, Sum.elim_inr]
  rw [hd, offSlotVector_square_sum]
  module

/-- The exact total square sum in the actual fourteen-dimensional traceless
Hermitian quaternionic space, for every real orthonormal basis. -/
theorem nativeTraceless_square_sum {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ TracelessHilbert) :
    (∑ i, nativeTracelessMatrix (e i) ^ 2) = (14 / 3 : ℝ) • (1 : QMat) :=
  (native_square_sum_basis_invariant e canonicalTracelessBasis).trans canonicalTracelessBasis_square_sum

end QuaternionicMUB
