module

public import ThirteenPlanes.Quaternionic.FrameGeometry
public import ThirteenPlanes.Quaternionic.JointEigenbasis

@[expose] public section

/-!
# Every ordinary quaternionic frame comes from actual basis columns

A trace-one Hermitian projection is rank one by positivity: normalize a nonzero
range column; its rank-one projector has the same range direction, and the
remaining Hermitian projection has trace zero, hence zero Frobenius square.
No spectral diagonalizer is stored in a frame or assumed by this dictionary.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma frobeniusSq_eq_zero_iff (P : QMat) : frobeniusSq P = 0 ↔ P = 0 := by
  constructor
  · intro h
    change (∑ i, ∑ j, Quaternion.normSq (P i j)) = 0 at h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Quaternion.normSq_nonneg)).mp h
    apply Matrix.ext
    intro i j
    have hi := hall i (Finset.mem_univ i)
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Quaternion.normSq_nonneg)).mp hi
    exact Quaternion.normSq_eq_zero.mp (hrow j (Finset.mem_univ j))
  · rintro rfl
    simp [frobeniusSq]

lemma hermitian_projection_trace_zero {P : QMat} (hP : P.IsHermitian)
    (hP2 : P * P = P) (htr : rtrace P = 0) : P = 0 := by
  apply (frobeniusSq_eq_zero_iff P).mp
  rw [← traceForm_self_eq_frobeniusSq hP, traceForm_eq_rtrace_mul, hP2, htr]

lemma mul_projector_apply (P : QMat) (u : QVec) (i j : Outcome) :
    (P * projector u) i j = matrixAction P u i * star (u j) := by
  simp only [Matrix.mul_apply, projector, matrixAction_apply, Matrix.mulVec,
    dotProduct, Finset.sum_mul, mul_assoc]

lemma projector_mul_of_fixed {P : QMat} (hP : P.IsHermitian) (u : QVec)
    (hu : matrixAction P u = u) :
    P * projector u = projector u ∧ projector u * P = projector u := by
  have hleft : P * projector u = projector u := by
    apply Matrix.ext
    intro i j
    rw [mul_projector_apply, hu]
    rfl
  refine ⟨hleft, ?_⟩
  have h := congrArg Matrix.conjTranspose hleft
  simpa only [Matrix.conjTranspose_mul, hP.eq, (projector_isHermitian u).eq] using h

/-- An arbitrary trace-one Hermitian projection is the actual projector of a
unit quaternion column, including every possible orientation of its range. -/
theorem trace_one_projection_has_column (P : QMat) (hP : P.IsHermitian)
    (hP2 : P * P = P) (htr : rtrace P = 1) :
    ∃ u : QHilbert, ‖u‖ = 1 ∧ P = projector (columnEquiv u) := by
  have hP0 : P ≠ 0 := by intro h; simpa [h] using htr
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hP0
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  change P i j ≠ 0 at hij
  let v : QHilbert := WithLp.toLp 2 (fun k => P k j)
  have hv0 : v ≠ 0 := by
    intro h
    have h' := congrArg (fun w : QHilbert => w i) h
    exact hij h'
  have hPv : realAction P v = v := by
    apply columnEquiv.injective
    rw [realAction_apply]
    funext k
    change (P * P) k j = P k j
    exact congrArg (fun A : QMat => A k j) hP2
  let u : QHilbert := ‖v‖⁻¹ • v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hu : ‖u‖ = 1 := by
    change ‖‖v‖⁻¹ • v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ hn]
  have hPu : realAction P u = u := by
    change realAction P (‖v‖⁻¹ • v) = ‖v‖⁻¹ • v
    rw [map_smul, hPv]
  have hfixed : matrixAction P (columnEquiv u) = columnEquiv u := by
    simpa only [realAction_apply] using congrArg columnEquiv hPu
  have hinner : qInner (columnEquiv u) (columnEquiv u) = 1 := by
    rw [qInner_self_eq_norm_sq, hu]
    norm_num
  let E := projector (columnEquiv u)
  have hE : E.IsHermitian := projector_isHermitian _
  have hE2 : E * E = E := projector_idempotent _ hinner
  obtain ⟨hPE, hEP⟩ := projector_mul_of_fixed hP (columnEquiv u) hfixed
  have htrE : rtrace E = 1 := by
    calc
      rtrace E = rtrace (E * E) := by rw [hE2]
      _ = Quaternion.normSq (qInner (columnEquiv u) (columnEquiv u)) :=
        rtrace_projector_mul _ _
      _ = 1 := by rw [hinner]; simp
  have hdiff2 : (P - E) * (P - E) = P - E := by
    calc
      (P - E) * (P - E) = (P * P - P * E) - (E * P - E * E) := by
        rw [sub_mul, mul_sub, mul_sub]
      _ = (P - E) - (E - E) := by rw [hP2, hPE, hEP, hE2]
      _ = P - E := by rw [sub_self, sub_zero]
  have hdifftr : rtrace (P - E) = 0 := by rw [rtrace_sub, htr, htrE]; norm_num
  have hdiff := hermitian_projection_trace_zero (hP.sub hE) hdiff2 hdifftr
  exact ⟨u, hu, sub_eq_zero.mp hdiff⟩

/-- The reverse ordinary-frame/basis dictionary, with no normal-form restriction
and no conclusion-bearing additional field in Frame. -/
theorem frame_has_basis (F : Frame) : ∃ U : QBasis, ∀ a, U.point a = F.point a := by
  classical
  have hp (a : Outcome) : ∃ u : QHilbert, ‖u‖ = 1 ∧
      F.point a = projector (columnEquiv u) :=
    trace_one_projection_has_column (F.point a) (F.hermitian a)
      (by simpa only [jordan_self] using F.idempotent a) (F.trace_one a)
  choose v hn hv using hp
  have ho : ∀ a b, a ≠ b → qInner (columnEquiv (v a)) (columnEquiv (v b)) = 0 := by
    intro a b hab
    apply Quaternion.normSq_eq_zero.mp
    rw [← traceForm_projector_projector, ← hv a, ← hv b, traceForm, F.orthogonal a b hab,
      rtrace_zero]
  let M := matrixOfColumns v
  have hM : Mᴴ * M = 1 := matrixOfColumns_adjoint_mul v hn ho
  let U : QBasis := ⟨M, hM, mul_adjoint_of_adjoint_mul M hM⟩
  refine ⟨U, ?_⟩
  intro a
  change projector (columnEquiv (v a)) = F.point a
  exact (hv a).symm

end QuaternionicMUB
