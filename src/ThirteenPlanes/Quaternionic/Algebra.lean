module

public import ThirteenPlanes.Quaternionic.Definitions
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Elementary native quaternionic matrix identities

Elementary proofs over the literal native carrier.
In particular real-trace cyclicity below is proved from quaternion coordinates;
it does not use the inapplicable commutative `Matrix.trace_mul_comm` theorem.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma quaternion_re_mul_comm (p q : Q) : (p * q).re = (q * p).re := by
  simp only [Quaternion.re_mul]
  ring

lemma quaternion_re_sum {ι : Type*} (t : Finset ι) (f : ι → Q) :
    (∑ i ∈ t, f i).re = ∑ i ∈ t, (f i).re := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [hi, ih]

@[simp] lemma rtrace_zero : rtrace 0 = 0 := by simp [rtrace]

@[simp] lemma rtrace_add (A B : QMat) : rtrace (A + B) = rtrace A + rtrace B :=
  rtraceLinear.map_add A B

@[simp] lemma rtrace_smul (r : ℝ) (A : QMat) : rtrace (r • A) = r * rtrace A :=
  rtraceLinear.map_smul r A

@[simp] lemma rtrace_one : rtrace 1 = 3 := by simp [rtrace]

@[simp] lemma rtrace_conjTranspose (A : QMat) : rtrace Aᴴ = rtrace A := by
  simp [rtrace, Matrix.conjTranspose_apply]

lemma rtrace_mul_comm (A B : QMat) : rtrace (A * B) = rtrace (B * A) := by
  simp only [rtrace, Matrix.mul_apply, quaternion_re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact quaternion_re_mul_comm _ _

lemma rtrace_mul_rotate (A B C : QMat) :
    rtrace (A * B * C) = rtrace (B * C * A) := by
  rw [mul_assoc, rtrace_mul_comm A (B * C)]

lemma traceForm_eq_rtrace_mul (A B : QMat) : traceForm A B = rtrace (A * B) := by
  rw [traceForm, jordan, rtrace_smul, rtrace_add, rtrace_mul_comm B A]
  ring

lemma traceForm_comm (A B : QMat) : traceForm A B = traceForm B A := by
  simp only [traceForm_eq_rtrace_mul]
  exact rtrace_mul_comm A B

lemma jordan_comm (A B : QMat) : jordan A B = jordan B A := by
  simp only [jordan, add_comm]

lemma jordan_self (A : QMat) : jordan A A = A * A := by
  rw [jordan, ← two_smul ℝ (A * A), smul_smul]
  norm_num

lemma jordan_isHermitian {A B : QMat} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (jordan A B).IsHermitian := by
  change ((1 / 2 : ℝ) • (A * B + B * A))ᴴ = (1 / 2 : ℝ) • (A * B + B * A)
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hA.eq, hB.eq]
  rw [add_comm]

lemma qInner_star (u v : QVec) : qInner v u = star (qInner u v) := by
  simp only [qInner, star_sum, star_mul, star_star]

lemma qInner_right_mul (u v : QVec) (p q : Q) :
    qInner (fun i => u i * p) (fun i => v i * q) = star p * qInner u v * q := by
  simp only [qInner, star_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

lemma projector_isHermitian (u : QVec) : (projector u).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [projector]

lemma projector_mul_apply (u v : QVec) (i j : Outcome) :
    (projector u * projector v) i j = u i * qInner u v * star (v j) := by
  simp only [Matrix.mul_apply, projector, qInner, Finset.mul_sum, Finset.sum_mul, mul_assoc]

lemma projector_idempotent (u : QVec) (hu : qInner u u = 1) :
    projector u * projector u = projector u := by
  apply Matrix.ext
  intro i j
  rw [projector_mul_apply, hu]
  simp [projector]

lemma rtrace_projector (u : QVec) : rtrace (projector u) = ∑ i, Quaternion.normSq (u i) := by
  simp only [rtrace, projector, Quaternion.normSq_def]

lemma rtrace_projector_mul (u v : QVec) :
    rtrace (projector u * projector v) = Quaternion.normSq (qInner u v) := by
  calc
    rtrace (projector u * projector v)
        = ∑ i, (u i * qInner u v * star (v i)).re := by
            simp only [rtrace, projector_mul_apply]
    _ = ∑ i, ((star (v i) * u i) * qInner u v).re := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [quaternion_re_mul_comm, ← mul_assoc]
    _ = ((∑ i, star (v i) * u i) * qInner u v).re := by
          rw [Finset.sum_mul, quaternion_re_sum]
    _ = Quaternion.normSq (qInner u v) := by
          change (qInner v u * qInner u v).re = _
          rw [qInner_star, Quaternion.star_mul_self]
          simp

lemma traceForm_projector_projector (u v : QVec) :
    traceForm (projector u) (projector v) = Quaternion.normSq (qInner u v) := by
  rw [traceForm_eq_rtrace_mul, rtrace_projector_mul]

lemma frobeniusSq_nonneg (A : QMat) : 0 ≤ frobeniusSq A := by
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj => Quaternion.normSq_nonneg

lemma rtrace_adjoint_mul_self (A : QMat) : rtrace (Aᴴ * A) = frobeniusSq A := by
  calc
    rtrace (Aᴴ * A) = ∑ i, ∑ j, Quaternion.normSq (A j i) := by
      simp only [rtrace, Matrix.mul_apply, quaternion_re_sum, Matrix.conjTranspose_apply]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [Quaternion.star_mul_self]
    _ = frobeniusSq A := by rw [Finset.sum_comm]; rfl

lemma traceForm_self_eq_frobeniusSq {A : QMat} (hA : A.IsHermitian) :
    traceForm A A = frobeniusSq A := by
  rw [traceForm_eq_rtrace_mul]
  calc
    rtrace (A * A) = rtrace (Aᴴ * A) := by rw [hA.eq]
    _ = frobeniusSq A := rtrace_adjoint_mul_self A

namespace QBasis

lemma column_gram (U : QBasis) (a b : Outcome) :
    qInner (U.column a) (U.column b) = if a = b then 1 else 0 := by
  change (U.matᴴ * U.mat) a b = _
  rw [U.adjoint_mul]
  simp [Matrix.one_apply]

lemma point_sum (U : QBasis) : ∑ a, U.point a = 1 := by
  apply Matrix.ext
  intro i j
  change (U.mat * U.matᴴ) i j = (1 : QMat) i j
  rw [U.mul_adjoint]

lemma point_isHermitian (U : QBasis) (a : Outcome) : (U.point a).IsHermitian :=
  projector_isHermitian (U.column a)

lemma point_idempotent (U : QBasis) (a : Outcome) : U.point a * U.point a = U.point a :=
  projector_idempotent (U.column a) (by simpa using U.column_gram a a)

end QBasis

end QuaternionicMUB
