module

public import ThirteenPlanes.Cartan.QuaternionJordan
public import ThirteenPlanes.Cartan.JordanAction
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

set_option backward.privateInPublic true

/-! Quaternionic unitary conjugation on the actual Jordan model. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped BigOperators Matrix RealInnerProductSpace

noncomputable section

private def adjointBasis (U : QBasis) : QBasis where
  mat := U.matᴴ
  adjoint_mul := by simpa using U.mul_adjoint
  mul_adjoint := by simpa using U.adjoint_mul

private theorem quaternion_conjugate_hermitian (U : QBasis) (x : HermitianHilbert) :
    (unitaryConjugate U (fullMat x)).IsHermitian := by
  change (U.matᴴ * fullMat x * U.mat)ᴴ = _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, (fullMat_hermitian x).eq,
    unitaryConjugate, mul_assoc]

private def quaternionConjugate (U : QBasis) (x : HermitianHilbert) : HermitianHilbert :=
  fullOfMatrix _ (quaternion_conjugate_hermitian U x)

@[simp] private theorem fullMat_quaternionConjugate (U : QBasis) (x : HermitianHilbert) :
    fullMat (quaternionConjugate U x) = unitaryConjugate U (fullMat x) :=
  fullMat_ofMatrix _ _

private theorem quaternionConjugate_leftInv (U : QBasis) (x : HermitianHilbert) :
    quaternionConjugate (adjointBasis U) (quaternionConjugate U x) = x := by
  apply fullMat_injective
  rw [fullMat_quaternionConjugate, fullMat_quaternionConjugate]
  simp only [unitaryConjugate, adjointBasis, Matrix.conjTranspose_conjTranspose,
    ← mul_assoc, U.mul_adjoint, one_mul]
  rw [mul_assoc, U.mul_adjoint, mul_one]

/-- The actual quaternionic unitary group acting by conjugation with U*. -/
def quaternionJordanAction (U : QBasis) : quaternionJordan.Automorphism where
  action :=
    { toFun := quaternionConjugate U
      invFun := quaternionConjugate (adjointBasis U)
      left_inv := quaternionConjugate_leftInv U
      right_inv := by
        intro x
        apply fullMat_injective
        rw [fullMat_quaternionConjugate, fullMat_quaternionConjugate]
        simp only [unitaryConjugate, adjointBasis, Matrix.conjTranspose_conjTranspose,
          ← mul_assoc, U.adjoint_mul, one_mul]
        rw [mul_assoc, U.adjoint_mul, mul_one]
      map_add' := by
        intro x y
        apply fullMat_injective
        simp only [map_add, fullMat_quaternionConjugate, unitaryConjugate, mul_add, add_mul]
      map_smul' := by
        intro r x
        apply fullMat_injective
        simp only [map_smul, fullMat_quaternionConjugate, unitaryConjugate,
          mul_smul_comm, smul_mul_assoc, RingHom.id_apply]
      norm_map' := by
        intro x
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          hermitianHilbert_inner, hermitianHilbert_inner]
        change traceForm (fullMat (quaternionConjugate U x)) (fullMat (quaternionConjugate U x)) =
          traceForm (fullMat x) (fullMat x)
        rw [fullMat_quaternionConjugate, traceForm_eq_rtrace_mul, traceForm_eq_rtrace_mul,
          ← unitaryConjugate_mul, rtrace_unitaryConjugate] }
  unit_fixed := by
    apply fullMat_injective
    change fullMat (quaternionConjugate U fullUnit) = fullMat fullUnit
    rw [fullMat_quaternionConjugate, fullMat_fullUnit, unitaryConjugate_one]
  product_map := by
    intro x y
    apply fullMat_injective
    change fullMat (quaternionConjugate U (quaternionFullCubic.L x y)) =
      fullMat (quaternionFullCubic.L (quaternionConjugate U x) (quaternionConjugate U y))
    simp only [fullMat_quaternionConjugate, quaternion_L_matrix, jordan]
    have h (X Y : QMat) : unitaryConjugate U ((1 / 2 : ℝ) • (X + Y)) =
        (1 / 2 : ℝ) • (unitaryConjugate U X + unitaryConjugate U Y) := by
      simp only [unitaryConjugate, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
    rw [h, unitaryConjugate_mul, unitaryConjugate_mul]

@[simp] theorem quaternionJordanAction_matrix (U : QBasis) (x : HermitianHilbert) :
    fullMat ((quaternionJordanAction U).action x) = unitaryConjugate U (fullMat x) :=
  fullMat_quaternionConjugate _ _

private abbrev quatV := quaternionJordan.traceFree
private abbrev qmat (x : quatV) := fullMat x.val

private theorem qmat_injective : Function.Injective qmat :=
  fullMat_injective.comp Subtype.val_injective

private abbrev qact (U : QBasis) : quatV ≃ₗᵢ[ℝ] quatV :=
  (quaternionJordanAction U).traceAction quaternionJordan

@[simp] theorem quaternionTraceAction_matrix (U : QBasis) (x : quatV) :
    qmat (qact U x) = unitaryConjugate U (qmat x) := quaternionJordanAction_matrix U x.val

private def signEntries (i k : Outcome) : Q := if k = i then -1 else 1

private def signBasis (i : Outcome) : QBasis where
  mat := Matrix.diagonal (signEntries i)
  adjoint_mul := by
    rw [Matrix.diagonal_conjTranspose]
    apply Matrix.ext
    intro a b
    rw [Matrix.diagonal_mul]
    by_cases h : a = b
    · subst b
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      by_cases h : a = i <;> simp [signEntries, h]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  mul_adjoint := by
    rw [Matrix.diagonal_conjTranspose]
    apply Matrix.ext
    intro a b
    rw [Matrix.diagonal_mul]
    by_cases h : a = b
    · subst b
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      by_cases h : a = i <;> simp [signEntries, h]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

private def permBasis (σ : Equiv.Perm Outcome) : QBasis where
  mat := σ.permMatrix Q
  adjoint_mul := by rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]
  mul_adjoint := by rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

private theorem qact_sign_entry (i : Outcome) (x : quatV) (a b : Outcome) :
    qmat (qact (signBasis i) x) a b = star (signEntries i a) * qmat x a b * signEntries i b := by
  rw [quaternionTraceAction_matrix]
  change ((Matrix.diagonal (signEntries i))ᴴ * qmat x * Matrix.diagonal (signEntries i)) a b = _
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

private theorem qact_perm_entry (σ : Equiv.Perm Outcome) (x : quatV) (a b : Outcome) :
    qmat (qact (permBasis σ) x) a b = qmat x (σ.symm a) (σ.symm b) := by
  rw [quaternionTraceAction_matrix]
  change ((σ.permMatrix Q)ᴴ * qmat x * σ.permMatrix Q) a b = _
  rw [Matrix.conjTranspose_permMatrix, mul_assoc, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

private def QDiagonal (x : quatV) : Prop := ∀ a b, a ≠ b → qmat x a b = 0

private theorem sign_fixed_diag (i : Outcome) {x : quatV} (h : QDiagonal x) :
    qact (signBasis i) x = x := by
  apply qmat_injective
  apply Matrix.ext
  intro a b
  rw [qact_sign_entry]
  by_cases hab : a = b
  · subst b
    by_cases ha : a = i <;> simp [signEntries, ha]
  · rw [h a b hab, mul_zero, zero_mul]

private theorem diag_of_sign_fixed {x : quatV} (h : ∀ i, qact (signBasis i) x = x) :
    QDiagonal x := by
  intro a b hab
  have he := congrArg (fun x : quatV => qmat x a b) (h a)
  rw [qact_sign_entry] at he
  have hn : -(qmat x a b) = qmat x a b := by simpa [signEntries, hab.symm] using he
  have hz : qmat x a b + qmat x a b = 0 := by
    calc
      _ = -(qmat x a b) + qmat x a b := congrArg (fun w : Q => w + qmat x a b) hn.symm
      _ = 0 := neg_add_cancel _
  have hz' : (2 : ℝ) • qmat x a b = 0 := by simpa only [two_smul] using hz
  exact (smul_eq_zero.mp hz').resolve_left (by norm_num)

private theorem quatRealDiagonal_hermitian (a : Outcome → ℝ) : (realDiagonal a).IsHermitian := by
  change (Matrix.diagonal (fun i => (a i : Q)))ᴴ = _
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  exact Quaternion.star_coe (a i)

private def quatDiagonal (a : Outcome → ℝ) (ha : ∑ i, a i = 0) : quatV :=
  quaternionTraceEquiv.symm (traceOfMatrix (realDiagonal a)
    (quatRealDiagonal_hermitian a) (by simpa [rtrace, realDiagonal] using ha))

@[simp] private theorem quatDiagonal_matrix (a : Outcome → ℝ) (ha : ∑ i, a i = 0) :
    qmat (quatDiagonal a ha) = realDiagonal a := by
  change fullMat (quatDiagonal a ha).val = _
  rw [← quaternionTraceEquiv_matrix]
  simp [quatDiagonal]

private def diff01 : quatV :=
  quatDiagonal ![1, -1, 0] (by norm_num [Fin.sum_univ_three])

private theorem diff01_swap :
    qact (permBasis (Equiv.swap (0 : Outcome) 1)) diff01 = -diff01 := by
  apply qmat_injective
  apply Matrix.ext
  intro a b
  rw [qact_perm_entry]
  change qmat diff01 ((Equiv.swap 0 1).symm a) ((Equiv.swap 0 1).symm b) =
    (-fullMat diff01.val) a b
  unfold diff01
  rw [quatDiagonal_matrix]
  fin_cases a <;> fin_cases b <;> simp [realDiagonal, Equiv.swap_apply_def]

private theorem qmat_diag_im_zero (x : quatV) (a : Outcome) :
    qmat x a a = ((qmat x a a).re : Q) := by
  have h := congrArg (fun A : QMat => A a a) (fullMat_hermitian x.val).eq
  change star (qmat x a a) = qmat x a a at h
  have hi : -(qmat x a a).imI = (qmat x a a).imI := congrArg (fun q : Q => q.imI) h
  have hj : -(qmat x a a).imJ = (qmat x a a).imJ := congrArg (fun q : Q => q.imJ) h
  have hk : -(qmat x a a).imK = (qmat x a a).imK := congrArg (fun q : Q => q.imK) h
  ext <;> simp <;> linarith

private theorem quat_smul_one (r : ℝ) : r • (1 : Q) = (r : Q) := by
  rw [Algebra.smul_def, mul_one]
  rfl

/-- Every real endomorphism commuting with the full quaternionic unitary action is scalar. -/
theorem quaternionJordan_commuting_eq_smul_id (S : Module.End ℝ quatV)
    (hS : ∀ (U : QBasis) (x : quatV), S (qact U x) = qact U (S x)) :
    ∃ a : ℝ, S = a • LinearMap.id := by
  have preserve (x : quatV) (hx : QDiagonal x) : QDiagonal (S x) := by
    apply diag_of_sign_fixed
    intro i
    rw [← hS, sign_fixed_diag i hx]
  let e := diff01
  let f := qact (permBasis (Equiv.swap (0 : Outcome) 2)) e
  have he : QDiagonal e := by
    intro i j hij
    simp [e, diff01, realDiagonal, Matrix.diagonal_apply_ne _ hij]
  have heS : QDiagonal (S e) := preserve e he
  have hSwap : qact (permBasis (Equiv.swap (0 : Outcome) 1)) (S e) = -(S e) := by
    rw [← hS, show e = diff01 from rfl, diff01_swap, map_neg]
  let a := (qmat (S e) 0 0).re
  have heScal : S e = a • e := by
    apply qmat_injective
    change fullMat (S e).val = fullMat (a • e).val
    rw [Submodule.coe_smul, map_smul]
    apply Matrix.ext
    intro i j
    change qmat (S e) i j = a • qmat e i j
    by_cases hij : i = j
    · subst j
      have h00 := qmat_diag_im_zero (S e) 0
      have h11 := congrArg (fun x : quatV => qmat x 0 0) hSwap
      have h22 := congrArg (fun x : quatV => qmat x 2 2) hSwap
      rw [qact_perm_entry] at h11 h22
      change qmat (S e) 1 1 = -(qmat (S e) 0 0) at h11
      change qmat (S e) 2 2 = -(qmat (S e) 2 2) at h22
      have hz : qmat (S e) 2 2 = 0 := by
        have h := congrArg (fun q : Q => q.re) h22
        change (qmat (S e) 2 2).re = -(qmat (S e) 2 2).re at h
        rw [qmat_diag_im_zero]
        have h0 : (qmat (S e) 2 2).re = 0 := by linarith
        simp [h0]
      have e0 : qmat e 0 0 = 1 := by simp [e, diff01, realDiagonal]
      have e1 : qmat e 1 1 = -1 := by simp [e, diff01, realDiagonal]
      have e2 : qmat e 2 2 = 0 := by simp [e, diff01, realDiagonal]
      fin_cases i
      · change qmat (S e) 0 0 = a • qmat e 0 0
        rw [e0, quat_smul_one]
        exact h00
      · change qmat (S e) 1 1 = a • qmat e 1 1
        rw [e1, smul_neg, quat_smul_one]
        exact h11.trans (congrArg Neg.neg h00)
      · change qmat (S e) 2 2 = a • qmat e 2 2
        rw [e2, smul_zero]
        exact hz
    · rw [heS i j hij, he i j hij, smul_zero]
  have hfScal : S f = a • f := by
    change S (qact (permBasis (Equiv.swap (0 : Outcome) 2)) e) = _
    rw [hS, heScal, map_smul]
  have hdiag (x : quatV) (hx : QDiagonal x) : S x = a • x := by
    let b := (qmat x 0 0).re
    let c := (qmat x 2 2).re
    have hre : (qmat x 1 1).re = -b - c := by
      have h := x.property
      change quaternionJordan.trace x.val = 0 at h
      rw [quaternionJordan_trace] at h
      simp only [rtrace, Fin.sum_univ_three] at h
      dsimp [b, c]
      linarith
    have hmat : x = b • e + c • f := by
      apply qmat_injective
      change fullMat x.val = fullMat (b • e.val + c • f.val)
      rw [map_add, map_smul, map_smul]
      apply Matrix.ext
      intro i j
      change qmat x i j = b • qmat e i j + c • qmat f i j
      change qmat x i j = b • qmat e i j +
        c • qmat (qact (permBasis (Equiv.swap (0 : Outcome) 2)) e) i j
      rw [qact_perm_entry]
      by_cases hij : i = j
      · subst j
        rw [qmat_diag_im_zero]
        change ((qmat x i i).re : Q) = _
        have hsw : (Equiv.swap (0 : Outcome) 2).symm 1 = 1 := by decide
        fin_cases i
        · simp [e, diff01, realDiagonal, b, quat_smul_one]
        · change ((qmat x 1 1).re : Q) = b • qmat e 1 1 +
            c • qmat e ((Equiv.swap (0 : Outcome) 2).symm 1) ((Equiv.swap (0 : Outcome) 2).symm 1)
          rw [hre, hsw]
          have hneg : qmat e 1 1 = -1 := by simp [e, diff01, realDiagonal]
          rw [hneg, smul_neg, smul_neg, quat_smul_one, quat_smul_one,
            Quaternion.coe_sub, Quaternion.coe_neg, sub_eq_add_neg]
        · simp [e, diff01, realDiagonal, c, quat_smul_one]
      · rw [hx i j hij, he i j hij, he _ _ (fun h => hij ((Equiv.swap 0 2).symm.injective h)),
          smul_zero, smul_zero, add_zero]
    conv_lhs => rw [hmat]
    rw [map_add, map_smul, map_smul, heScal, hfScal, smul_comm b a, smul_comm c a,
      ← smul_add, ← hmat]
  refine ⟨a, LinearMap.ext fun x => ?_⟩
  obtain ⟨U, r, _, hU, _⟩ := commuting_hermitian_simultaneous_diagonalization
    (qmat x) 0 (fullMat_hermitian x.val) Matrix.isHermitian_zero (Commute.zero_right _)
  have hDiag : QDiagonal (qact U x) := by
    intro i j hij
    rw [quaternionTraceAction_matrix, unitaryConjugate, hU]
    simp [realDiagonal, Matrix.diagonal_apply_ne _ hij]
  apply (qact U).injective
  rw [← hS, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  exact hdiag _ hDiag

end

end ThirteenPlanes.Cartan
