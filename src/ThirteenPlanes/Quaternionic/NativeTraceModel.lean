module

public import ThirteenPlanes.Basic
public import ThirteenPlanes.Quaternionic.Capacity
public import ThirteenPlanes.Quaternionic.Quartic
public import ThirteenPlanes.Quaternionic.PairProducts

@[expose] public section

set_option backward.privateInPublic true

/-! The trace-metric cubic of the native quaternionic Hermitian carrier. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace QuaternionicMUB

open ThirteenPlanes

noncomputable section

/-- The literal native quaternion matrix of a point of the Hermitian Hilbert space. -/
def fullMat : HermitianHilbert →ₗ[ℝ] QMat :=
  matrixHilbertEquiv.toLinearMap.comp hermitianHilbertSubmodule.subtype

/-- The literal native matrix of a point of the trace-zero Hilbert space. -/
def traceMat : TracelessHilbert →ₗ[ℝ] QMat :=
  matrixHilbertEquiv.toLinearMap.comp tracelessHilbertSubmodule.subtype

theorem fullMat_injective : Function.Injective fullMat :=
  matrixHilbertEquiv.injective.comp Subtype.val_injective

theorem traceMat_injective : Function.Injective traceMat :=
  matrixHilbertEquiv.injective.comp Subtype.val_injective

theorem fullMat_hermitian (x : HermitianHilbert) : (fullMat x).IsHermitian := x.property

theorem traceMat_hermitian (x : TracelessHilbert) : (traceMat x).IsHermitian := x.property.1

theorem traceMat_trace (x : TracelessHilbert) : rtrace (traceMat x) = 0 := x.property.2

/-- The isometric inclusion of the trace-zero space into the unital space. -/
def traceInclusion : TracelessHilbert →ₗᵢ[ℝ] HermitianHilbert :=
  ⟨Submodule.inclusion (fun _ h => h.1), fun _ => rfl⟩

@[simp] theorem fullMat_traceInclusion (x : TracelessHilbert) :
    fullMat (traceInclusion x) = traceMat x := rfl

/-- A Hermitian matrix with its trace metric. -/
def fullOfMatrix (A : QMat) (hA : A.IsHermitian) : HermitianHilbert :=
  hermitianHilbertEquiv.symm ⟨A, hA⟩

@[simp] theorem fullMat_ofMatrix (A : QMat) (hA : A.IsHermitian) :
    fullMat (fullOfMatrix A hA) = A :=
  congrArg Subtype.val (hermitianHilbertEquiv.apply_symm_apply ⟨A, hA⟩)

/-- A traceless Hermitian matrix with its trace metric. -/
def traceOfMatrix (A : QMat) (hA : A.IsHermitian) (ht : rtrace A = 0) : TracelessHilbert :=
  tracelessHilbertEquiv.symm ⟨A, hA, ht⟩

@[simp] theorem traceMat_ofMatrix (A : QMat) (hA : A.IsHermitian) (ht : rtrace A = 0) :
    traceMat (traceOfMatrix A hA ht) = A :=
  congrArg Subtype.val (tracelessHilbertEquiv.apply_symm_apply ⟨A, hA, ht⟩)

def fullUnit : HermitianHilbert := fullOfMatrix 1 Matrix.isHermitian_one

@[simp] theorem fullMat_fullUnit : fullMat fullUnit = 1 := fullMat_ofMatrix _ _

private theorem jordan_add_left (A B C : QMat) :
    jordan (A + B) C = jordan A C + jordan B C := by
  unfold jordan
  rw [add_mul, mul_add, ← smul_add]
  abel

private theorem jordan_smul_left (r : ℝ) (A B : QMat) :
    jordan (r • A) B = r • jordan A B := by
  unfold jordan
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_comm (1 / 2 : ℝ) r]

private def fullJordan (x y : HermitianHilbert) : HermitianHilbert :=
  fullOfMatrix (jordan (fullMat x) (fullMat y))
    (jordan_isHermitian (fullMat_hermitian x) (fullMat_hermitian y))

private theorem fullMat_jordan (x y : HermitianHilbert) :
    fullMat (fullJordan x y) = jordan (fullMat x) (fullMat y) :=
  fullMat_ofMatrix _ _

private def fullJordanBilin : HermitianHilbert →ₗ[ℝ] HermitianHilbert →ₗ[ℝ] HermitianHilbert :=
  LinearMap.mk₂ ℝ fullJordan
    (by
      intro x y z
      apply fullMat_injective
      simp only [fullMat_jordan, map_add, jordan_add_left])
    (by
      intro r x y
      apply fullMat_injective
      simp only [fullMat_jordan, map_smul, jordan_smul_left])
    (by
      intro x y z
      apply fullMat_injective
      simp only [fullMat_jordan, map_add]
      rw [jordan_comm (fullMat x), jordan_add_left, jordan_comm (fullMat y), jordan_comm (fullMat z)])
    (by
      intro r x y
      apply fullMat_injective
      simp only [fullMat_jordan, map_smul]
      rw [jordan_comm (fullMat x), jordan_smul_left, jordan_comm (fullMat y)])

/-- The actual Jordan product represented as a cubic on the rank-three unital algebra. -/
def quaternionFullCubic : SymmetricCubic HermitianHilbert :=
  SymmetricCubic.ofProduct fullJordanBilin
    (by
      intro x y
      apply fullMat_injective
      change fullMat (fullJordan x y) = fullMat (fullJordan y x)
      rw [fullMat_jordan, fullMat_jordan, jordan_comm])
    (by
      intro x y z
      change ⟪fullJordan x y, z⟫ = ⟪fullJordan x z, y⟫
      rw [hermitianHilbert_inner, hermitianHilbert_inner]
      change traceForm (fullMat (fullJordan x y)) (fullMat z) =
        traceForm (fullMat (fullJordan x z)) (fullMat y)
      rw [fullMat_jordan, fullMat_jordan, traceForm_jordan_assoc,
        traceForm_jordan_assoc, jordan_comm (fullMat y)])

theorem quaternionFullCubic_unit (x : HermitianHilbert) :
    quaternionFullCubic.L fullUnit x = x := by
  apply fullMat_injective
  change fullMat (fullJordan fullUnit x) = fullMat x
  rw [fullMat_jordan, fullMat_fullUnit]
  simp [jordan, ← two_smul ℝ, smul_smul]

theorem quaternionFullCubic_apply (x y z : HermitianHilbert) :
    quaternionFullCubic.apply x y z = rtrace (jordan (jordan (fullMat x) (fullMat y)) (fullMat z)) := by
  change ⟪fullJordan x y, z⟫ = _
  rw [hermitianHilbert_inner]
  change traceForm (fullMat (fullJordan x y)) (fullMat z) = _
  rw [fullMat_jordan]
  rfl

/-- The native trace-zero cubic is the induced restriction of the full product. -/
def quaternionTraceCubic : SymmetricCubic TracelessHilbert :=
  quaternionFullCubic.pullback traceInclusion.toLinearMap

theorem quaternionTraceCubic_apply (x y z : TracelessHilbert) :
    quaternionTraceCubic.apply x y z =
      quaternionFullCubic.apply (traceInclusion x) (traceInclusion y) (traceInclusion z) :=
  SymmetricCubic.pullback_apply _ _ _ _ _

/-- Native trace projection onto the traceless summand. -/
def centerMatrix (A : QMat) : QMat := A - (rtrace A / 3) • (1 : QMat)

theorem centerMatrix_hermitian {A : QMat} (hA : A.IsHermitian) :
    (centerMatrix A).IsHermitian := by
  change (centerMatrix A)ᴴ = _
  simp only [centerMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    hA.eq, star_trivial, Matrix.conjTranspose_one]

theorem centerMatrix_trace (A : QMat) : rtrace (centerMatrix A) = 0 := by
  rw [centerMatrix, rtrace_sub, rtrace_smul, rtrace_one]
  ring

theorem quaternionTraceCubic_L_matrix (x y : TracelessHilbert) :
    traceMat (quaternionTraceCubic.L x y) = centerMatrix (jordan (traceMat x) (traceMat y)) := by
  let A := jordan (traceMat x) (traceMat y)
  let w := traceOfMatrix (centerMatrix A)
    (centerMatrix_hermitian (jordan_isHermitian (traceMat_hermitian x) (traceMat_hermitian y)))
    (centerMatrix_trace A)
  have hw : quaternionTraceCubic.L x y = w := by
    apply ext_inner_right ℝ
    intro z
    change quaternionTraceCubic.apply x y z = ⟪w, z⟫
    rw [quaternionTraceCubic_apply, quaternionFullCubic_apply, tracelessHilbert_inner]
    change rtrace (jordan A (traceMat z)) = traceForm (traceMat w) (traceMat z)
    rw [show traceMat w = centerMatrix A from traceMat_ofMatrix _ _ _,
      centerMatrix, traceForm_sub_left, traceForm_smul_left, traceForm_eq_rtrace_mul 1,
      one_mul, traceMat_trace, mul_zero, sub_zero]
    rfl
  rw [hw]
  exact traceMat_ofMatrix _ _ _

/-- The rank-three trace quartic gives the round strength of the native cubic. -/
theorem quaternionTraceCubic_round : IsRound quaternionTraceCubic (1 / 6) := by
  refine ⟨by norm_num, fun x => ?_⟩
  let A := traceMat x
  let b := rtrace (A ^ 2)
  let k := b / 3
  have hx : ‖x‖ ^ 2 = b := by
    rw [← real_inner_self_eq_norm_sq, tracelessHilbert_inner]
    change traceForm A A = _
    rw [traceForm_eq_rtrace_mul]
    exact congrArg rtrace (pow_two A).symm
  have hA4 : rtrace (A ^ 4) = (1 / 2 : ℝ) * b ^ 2 :=
    traceless_quartic A (traceMat_hermitian x) (traceMat_trace x)
  have hs : traceMat (quaternionTraceCubic.squareMap x) = A ^ 2 - k • (1 : QMat) := by
    rw [SymmetricCubic.squareMap, quaternionTraceCubic_L_matrix, jordan_self]
    change centerMatrix (A * A) = A ^ 2 - k • (1 : QMat)
    rw [← pow_two, centerMatrix]
  calc
    _ = rtrace ((A ^ 2 - k • (1 : QMat)) * (A ^ 2 - k • (1 : QMat))) := by
      rw [← real_inner_self_eq_norm_sq, tracelessHilbert_inner]
      change traceForm (traceMat (quaternionTraceCubic.squareMap x))
        (traceMat (quaternionTraceCubic.squareMap x)) = _
      rw [traceForm_eq_rtrace_mul, hs]
    _ = rtrace (A ^ 4) - 2 * k * b + k ^ 2 * 3 := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        rtrace_sub, rtrace_smul, rtrace_one, ← pow_add]
      change rtrace (A ^ 4) - k * b - (k * b - k * (k * 3)) = _
      ring
    _ = (1 / 6 : ℝ) * ‖x‖ ^ 4 := by
      have hx4 : ‖x‖ ^ 4 = b ^ 2 := by
        calc
          _ = (‖x‖ ^ 2) ^ 2 := by ring
          _ = _ := by rw [hx]
      rw [hA4, hx4]
      dsimp only [k]
      ring

end

end QuaternionicMUB
