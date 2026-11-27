module

public import ThirteenPlanes.Quaternionic.Algebra
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Native quaternionic frame geometry

The basis-to-frame dictionary and centered trace pairing below concern the actual
quaternionic matrices in Definitions. No dimension, positivity, capacity or
spectral conclusion is included as a hypothesis or definition field.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma rtrace_sub (A B : QMat) : rtrace (A - B) = rtrace A - rtrace B :=
  rtraceLinear.map_sub A B

lemma traceForm_sub_left (A B C : QMat) :
    traceForm (A - B) C = traceForm A C - traceForm B C := by
  simp only [traceForm_eq_rtrace_mul, sub_mul, rtrace_sub]

lemma traceForm_sub_right (A B C : QMat) :
    traceForm A (B - C) = traceForm A B - traceForm A C := by
  rw [traceForm_comm A, traceForm_sub_left, traceForm_comm B A, traceForm_comm C A]

lemma traceForm_smul_left (r : ℝ) (A B : QMat) :
    traceForm (r • A) B = r * traceForm A B := by
  simp only [traceForm_eq_rtrace_mul, smul_mul_assoc, rtrace_smul]

lemma traceForm_smul_right (r : ℝ) (A B : QMat) :
    traceForm A (r • B) = r * traceForm A B := by
  rw [traceForm_comm A, traceForm_smul_left, traceForm_comm B A]

@[simp] lemma traceForm_one_right (A : QMat) : traceForm A 1 = rtrace A := by
  rw [traceForm_eq_rtrace_mul, mul_one]

@[simp] lemma traceForm_one_left (A : QMat) : traceForm 1 A = rtrace A := by
  rw [traceForm_comm, traceForm_one_right]

lemma traceForm_centered (A B : QMat) (c : ℝ) :
    traceForm (A - c • 1) (B - c • 1) =
      traceForm A B - c * rtrace A - c * rtrace B + 3 * c ^ 2 := by
  simp only [traceForm_sub_left, traceForm_sub_right, traceForm_smul_left,
    traceForm_smul_right, traceForm_one_left, traceForm_one_right,
    rtrace_sub, rtrace_smul, rtrace_one]
  ring

namespace QBasis

lemma point_mul_eq_zero (U : QBasis) {a b : Outcome} (hab : a ≠ b) :
    U.point a * U.point b = 0 := by
  apply Matrix.ext
  intro i j
  change (projector (U.column a) * projector (U.column b)) i j = 0
  rw [projector_mul_apply, U.column_gram, if_neg hab]
  simp

lemma point_trace_one (U : QBasis) (a : Outcome) : rtrace (U.point a) = 1 := by
  calc
    rtrace (U.point a) = rtrace (U.point a * U.point a) := by
      rw [U.point_idempotent]
    _ = Quaternion.normSq (qInner (U.column a) (U.column a)) :=
      rtrace_projector_mul _ _
    _ = 1 := by rw [U.column_gram]; simp

/-- The actual three column projectors satisfy exactly the source frame axioms. -/
def toFrame (U : QBasis) : Frame where
  point := U.point
  hermitian := U.point_isHermitian
  trace_one := U.point_trace_one
  idempotent := fun a => by rw [jordan_self, U.point_idempotent]
  orthogonal := fun a b hab => by
    rw [jordan, U.point_mul_eq_zero hab, U.point_mul_eq_zero hab.symm]
    simp
  sum_points := U.point_sum

@[simp] lemma toFrame_point (U : QBasis) (a : Outcome) :
    U.toFrame.point a = U.point a := rfl

lemma mutuallyUnbiased_iff_toFrame (U V : QBasis) :
    U.MutuallyUnbiased V ↔ U.toFrame.MutuallyUnbiased V.toFrame := by
  simp only [QBasis.MutuallyUnbiased, Frame.MutuallyUnbiased, toFrame_point,
    QBasis.point, traceForm_projector_projector]

lemma not_mutuallyUnbiased_self (U : QBasis) : ¬ U.MutuallyUnbiased U := by
  intro h
  have h0 := h 0 0
  rw [U.column_gram] at h0
  norm_num at h0

end QBasis

namespace Frame

lemma traceForm_points (F : Frame) (a b : Outcome) :
    traceForm (F.point a) (F.point b) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    rw [traceForm, F.idempotent, F.trace_one]
    simp
  · rw [traceForm, F.orthogonal a b hab, rtrace_zero, if_neg hab]

/-- Centering takes place inside the literal native quaternionic matrix space. -/
def centeredPointMatrix (F : Frame) (a : Outcome) : QMat :=
  F.point a - (1 / 3 : ℝ) • 1

lemma centeredPointMatrix_isHermitian (F : Frame) (a : Outcome) :
    (F.centeredPointMatrix a).IsHermitian := by
  unfold centeredPointMatrix
  apply (F.hermitian a).sub
  apply Matrix.IsHermitian.smul Matrix.isHermitian_one
  rfl

lemma centeredPointMatrix_trace_zero (F : Frame) (a : Outcome) :
    rtrace (F.centeredPointMatrix a) = 0 := by
  simp [centeredPointMatrix, rtrace_sub, rtrace_smul, F.trace_one]

/-- Actual centered projectors, valued in the native trace-zero submodule. -/
def centeredPoint (F : Frame) (a : Outcome) : J0 :=
  ⟨F.centeredPointMatrix a,
    F.centeredPointMatrix_isHermitian a, F.centeredPointMatrix_trace_zero a⟩

lemma centeredPoint_gram (F : Frame) (a b : Outcome) :
    traceForm (F.centeredPointMatrix a) (F.centeredPointMatrix b) =
      (if a = b then 1 else 0) - (1 / 3 : ℝ) := by
  rw [centeredPointMatrix, centeredPointMatrix, traceForm_centered,
    F.trace_one, F.trace_one, F.traceForm_points]
  ring

lemma centeredPoint_cross_gram (F G : Frame) (a b : Outcome) :
    traceForm (F.centeredPointMatrix a) (G.centeredPointMatrix b) =
      traceForm (F.point a) (G.point b) - (1 / 3 : ℝ) := by
  rw [centeredPointMatrix, centeredPointMatrix, traceForm_centered,
    F.trace_one, G.trace_one]
  ring

lemma mutuallyUnbiased_iff_centered_orthogonal (F G : Frame) :
    F.MutuallyUnbiased G ↔
      ∀ a b, traceForm (F.centeredPointMatrix a) (G.centeredPointMatrix b) = 0 := by
  simp only [Frame.MutuallyUnbiased, centeredPoint_cross_gram, sub_eq_zero]

end Frame

end QuaternionicMUB
