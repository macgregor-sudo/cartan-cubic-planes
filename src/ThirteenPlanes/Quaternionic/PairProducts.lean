module

public import ThirteenPlanes.Quaternionic.FrameGeometry
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Native pair-product identities

The associative quaternion matrix Jordan product has its exact trace form.
These internal identities are proved on that carrier; rank-one hypotheses are
discharged for actual basis projectors rather than supplied to a headline bound.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma traceForm_add_left (A B C : QMat) :
    traceForm (A + B) C = traceForm A C + traceForm B C := by
  simp only [traceForm_eq_rtrace_mul, add_mul, rtrace_add]

lemma traceForm_add_right (A B C : QMat) :
    traceForm A (B + C) = traceForm A B + traceForm A C := by
  simp only [traceForm_eq_rtrace_mul, mul_add, rtrace_add]

lemma traceForm_jordan_assoc (A B C : QMat) :
    traceForm (jordan A B) C = traceForm A (jordan B C) := by
  simp only [traceForm_eq_rtrace_mul, jordan, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_add, rtrace_smul, rtrace_add, mul_assoc]
  rw [rtrace_mul_comm B (A * C), mul_assoc]

lemma jordan_U_identity (P Q : QMat) :
    (2 : ℝ) • jordan P (jordan P Q) - jordan (P * P) Q = P * Q * P := by
  simp only [jordan, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul,
    smul_add, mul_assoc]
  module

lemma projector_triple (u v : QVec) :
    projector u * projector v * projector u =
      Quaternion.normSq (qInner u v) • projector u := by
  apply Matrix.ext
  intro i j
  calc
    (projector u * projector v * projector u) i j =
        u i * (qInner u v * qInner v u) * star (u j) := by
      simp only [Matrix.mul_apply, projector_mul_apply, projector, qInner,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = Quaternion.normSq (qInner u v) • (projector u i j) := by
      change u i * (qInner u v * qInner v u) * star (u j) =
        Quaternion.normSq (qInner u v) • (u i * star (u j))
      have hs : qInner v u = star (qInner u v) := qInner_star u v
      rw [hs, Quaternion.self_mul_star, Quaternion.mul_coe_eq_smul, smul_mul_assoc]

lemma QBasis.point_triple {U V : QBasis} (hUV : U.MutuallyUnbiased V)
    (a b : Outcome) :
    U.point a * V.point b * U.point a = (1 / 3 : ℝ) • U.point a := by
  change projector (U.column a) * projector (V.column b) * projector (U.column a) =
    (1 / 3 : ℝ) • projector (U.column a)
  rw [projector_triple, hUV a b]

lemma traceForm_jordan_projectors_self (P Q : QMat)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (ht : traceForm P Q = (1 / 3 : ℝ))
    (hPQP : P * Q * P = (1 / 3 : ℝ) • P) :
    traceForm (jordan P Q) (jordan P Q) = (2 / 9 : ℝ) := by
  have hU := jordan_U_identity P Q
  rw [hP, hPQP] at hU
  have h := congrArg (fun A => traceForm A Q) hU
  rw [traceForm_sub_left, traceForm_smul_left, traceForm_smul_left] at h
  have h1 : traceForm (jordan P Q) Q = traceForm P Q := by
    rw [traceForm_jordan_assoc, jordan_self, hQ]
  have h2 : traceForm (jordan P (jordan P Q)) Q =
      traceForm (jordan P Q) (jordan P Q) := by
    rw [jordan_comm P (jordan P Q), traceForm_jordan_assoc]
  rw [h1, h2, ht] at h
  linarith

lemma traceForm_centered_pair_square (P Q : QMat)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (htrP : rtrace P = 1) (htrQ : rtrace Q = 1)
    (ht : traceForm P Q = (1 / 3 : ℝ))
    (hPQP : P * Q * P = (1 / 3 : ℝ) • P) :
    traceForm (jordan (P - (1 / 3 : ℝ) • 1) (Q - (1 / 3 : ℝ) • 1))
      (jordan (P - (1 / 3 : ℝ) • 1) (Q - (1 / 3 : ℝ) • 1)) = (1 / 27 : ℝ) := by
  have hM :
      jordan (P - (1 / 3 : ℝ) • 1) (Q - (1 / 3 : ℝ) • 1) =
        jordan P Q - (1 / 3 : ℝ) • (P + Q) + (1 / 9 : ℝ) • 1 := by
    simp only [jordan, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, smul_smul]
    module
  have hnorm := traceForm_jordan_projectors_self P Q hP hQ ht hPQP
  have hPQ_P : traceForm (jordan P Q) P = (1 / 3 : ℝ) := by
    rw [jordan_comm, traceForm_jordan_assoc, jordan_self, hP, traceForm_comm, ht]
  have hPQ_Q : traceForm (jordan P Q) Q = (1 / 3 : ℝ) := by
    rw [traceForm_jordan_assoc, jordan_self, hQ, ht]
  have hPP : traceForm P P = 1 := by rw [traceForm_eq_rtrace_mul, hP, htrP]
  have hQQ : traceForm Q Q = 1 := by rw [traceForm_eq_rtrace_mul, hQ, htrQ]
  have htrPQ : rtrace (jordan P Q) = (1 / 3 : ℝ) := ht
  rw [hM]
  simp only [traceForm_add_left, traceForm_add_right, traceForm_sub_left,
    traceForm_sub_right, traceForm_smul_left, traceForm_smul_right,
    traceForm_one_left, traceForm_one_right, rtrace_add, rtrace_sub,
    rtrace_smul, rtrace_one, hnorm, hPQ_P, hPQ_Q, hPP, hQQ, ht, htrP, htrQ, htrPQ,
    traceForm_comm P (jordan P Q), traceForm_comm Q (jordan P Q), traceForm_comm Q P]
  norm_num

lemma QBasis.centered_pair_square {U V : QBasis} (hUV : U.MutuallyUnbiased V)
    (a b : Outcome) :
    traceForm (jordan (U.toFrame.centeredPointMatrix a) (V.toFrame.centeredPointMatrix b))
      (jordan (U.toFrame.centeredPointMatrix a) (V.toFrame.centeredPointMatrix b)) =
        (1 / 27 : ℝ) := by
  apply traceForm_centered_pair_square
  · exact U.point_idempotent a
  · exact V.point_idempotent b
  · exact U.point_trace_one a
  · exact V.point_trace_one b
  · exact ((U.mutuallyUnbiased_iff_toFrame V).mp hUV) a b
  · exact U.point_triple hUV a b

end QuaternionicMUB
