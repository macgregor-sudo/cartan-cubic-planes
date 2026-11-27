module

public import ThirteenPlanes.Quaternionic.Spectral
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-! # Native quaternionic simultaneous unitary diagonalization -/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma exists_unit_joint_eigenvector_on {A B : QMat}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B)
    (S : Submodule ℝ QHilbert) (hS : S ≠ ⊥)
    (hAS : ∀ v ∈ S, realAction A v ∈ S)
    (hBS : ∀ v ∈ S, realAction B v ∈ S) :
    ∃ v : QHilbert, v ∈ S ∧ ‖v‖ = 1 ∧ ∃ a b : ℝ,
      realAction A v = a • v ∧ realAction B v = b • v := by
  obtain ⟨v, hvS, hv0, a, b, ha, hb⟩ :=
    exists_joint_eigenvector_on hA hB hAB S hS hAS hBS
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  refine ⟨‖v‖⁻¹ • v, S.smul_mem _ hvS, ?_, a, b, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ hn]
  · rw [map_smul, ha, smul_comm]
  · rw [map_smul, hb, smul_comm]

/-- Three normalized common quaternion columns, including all repeated-eigenvalue
cases. Two actual quaternion lines are removed in real dimensions 12→8→4. -/
lemma exists_orthonormal_joint_columns {A B : QMat}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ v : Outcome → QHilbert, ∃ a b : Outcome → ℝ,
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → qInner (columnEquiv (v i)) (columnEquiv (v j)) = 0) ∧
      (∀ i, realAction A (v i) = a i • v i) ∧
      (∀ i, realAction B (v i) = b i • v i) := by
  classical
  obtain ⟨v0, hv0mem, hn0, a0, b0, ha0, hb0⟩ :=
    exists_unit_joint_eigenvector_on hA hB hAB ⊤ top_ne_bot
      (by intro v hv; trivial) (by intro v hv; trivial)
  have hv0 : v0 ≠ 0 := by intro h; simpa [h] using hn0
  let S1 : Submodule ℝ QHilbert := (rightLine v0)ᗮ
  have hd1 : Module.finrank ℝ S1 = 8 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [finrank_rightLine hv0, finrank_QHilbert]
  have hS1 : S1 ≠ ⊥ := by
    intro h
    have hz := congrArg (fun S : Submodule ℝ QHilbert => Module.finrank ℝ S) h
    rw [hd1] at hz
    norm_num at hz
  have hr1 : RightStable S1 := rightStable_rightLine_orthogonal v0
  have hA1 : ∀ v ∈ S1, realAction A v ∈ S1 := rightLine_orthogonal_invariant hA ha0
  have hB1 : ∀ v ∈ S1, realAction B v ∈ S1 := rightLine_orthogonal_invariant hB hb0
  obtain ⟨v1, hv1mem, hn1, a1, b1, ha1, hb1⟩ :=
    exists_unit_joint_eigenvector_on hA hB hAB S1 hS1 hA1 hB1
  have hv1 : v1 ≠ 0 := by intro h; simpa [h] using hn1
  let S2 : Submodule ℝ QHilbert := (rightLine v1)ᗮ ⊓ S1
  have hd2 : Module.finrank ℝ S2 = 4 := by
    apply Submodule.finrank_add_inf_finrank_orthogonal' (rightLine_le hr1 hv1mem)
    rw [finrank_rightLine hv1, hd1]
  have hS2 : S2 ≠ ⊥ := by
    intro h
    have hz := congrArg (fun S : Submodule ℝ QHilbert => Module.finrank ℝ S) h
    rw [hd2] at hz
    norm_num at hz
  have hA2 : ∀ v ∈ S2, realAction A v ∈ S2 := by
    intro v hv
    exact ⟨rightLine_orthogonal_invariant hA ha1 v hv.1, hA1 v hv.2⟩
  have hB2 : ∀ v ∈ S2, realAction B v ∈ S2 := by
    intro v hv
    exact ⟨rightLine_orthogonal_invariant hB hb1 v hv.1, hB1 v hv.2⟩
  obtain ⟨v2, hv2mem, hn2, a2, b2, ha2, hb2⟩ :=
    exists_unit_joint_eigenvector_on hA hB hAB S2 hS2 hA2 hB2
  have h01 : qInner (columnEquiv v0) (columnEquiv v1) = 0 :=
    (mem_rightLine_orthogonal_iff v0 v1).mp hv1mem
  have h02 : qInner (columnEquiv v0) (columnEquiv v2) = 0 :=
    (mem_rightLine_orthogonal_iff v0 v2).mp hv2mem.2
  have h12 : qInner (columnEquiv v1) (columnEquiv v2) = 0 :=
    (mem_rightLine_orthogonal_iff v1 v2).mp hv2mem.1
  have h10 : qInner (columnEquiv v1) (columnEquiv v0) = 0 := by rw [qInner_star, h01, star_zero]
  have h20 : qInner (columnEquiv v2) (columnEquiv v0) = 0 := by rw [qInner_star, h02, star_zero]
  have h21 : qInner (columnEquiv v2) (columnEquiv v1) = 0 := by rw [qInner_star, h12, star_zero]
  refine ⟨![v0, v1, v2], ![a0, a1, a2], ![b0, b1, b2], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i <;> assumption

/-- The second native unitarity equation follows from the first using finite real
endomorphisms and the faithful action; no commutative quaternion determinant. -/
lemma mul_adjoint_of_adjoint_mul (U : QMat) (hU : Uᴴ * U = 1) : U * Uᴴ = 1 := by
  apply realAction_injective
  rw [realAction_mul, realAction_one]
  have h := congrArg realAction hU
  rw [realAction_mul, realAction_one] at h
  exact (LinearMap.comp_eq_id_comm ℝ QHilbert).mp h

def matrixOfColumns (v : Outcome → QHilbert) : QMat := fun i j => v j i

lemma matrixOfColumns_adjoint_mul (v : Outcome → QHilbert)
    (hn : ∀ i, ‖v i‖ = 1)
    (ho : ∀ i j, i ≠ j → qInner (columnEquiv (v i)) (columnEquiv (v j)) = 0) :
    (matrixOfColumns v)ᴴ * matrixOfColumns v = 1 := by
  apply Matrix.ext
  intro i j
  change qInner (columnEquiv (v i)) (columnEquiv (v j)) = (1 : QMat) i j
  by_cases hij : i = j
  · subst j
    rw [qInner_self_eq_norm_sq, hn i]
    simp
  · rw [ho i j hij]
    simp [Matrix.one_apply, hij]

lemma matrixOfColumns_eigenvectors (A : QMat) (v : Outcome → QHilbert) (a : Outcome → ℝ)
    (ha : ∀ j, realAction A (v j) = a j • v j) :
    A * matrixOfColumns v = matrixOfColumns v * realDiagonal a := by
  apply Matrix.ext
  intro i j
  have h := congrArg (fun w : QHilbert => w i) (ha j)
  change (A *ᵥ columnEquiv (v j)) i = a j • v j i at h
  rw [realDiagonal, Matrix.mul_diagonal, Quaternion.mul_coe_eq_smul]
  exact h

lemma adjoint_conjugate_eq_diagonal (U : QBasis) (A : QMat) (a : Outcome → ℝ)
    (h : A * U.mat = U.mat * realDiagonal a) : U.matᴴ * A * U.mat = realDiagonal a := by
  calc
    U.matᴴ * A * U.mat = U.matᴴ * (A * U.mat) := mul_assoc _ _ _
    _ = U.matᴴ * (U.mat * realDiagonal a) := by rw [h]
    _ = (U.matᴴ * U.mat) * realDiagonal a := (mul_assoc _ _ _).symm
    _ = realDiagonal a := by rw [U.adjoint_mul, one_mul]

/-- Every commuting pair of actual quaternionic Hermitian qutrit matrices is
simultaneously diagonalized by an actual two-sided quaternionic unitary.
This is the native spectral return, with no simple-spectrum assumption. -/
theorem commuting_hermitian_simultaneous_diagonalization
    (A B : QMat) (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U : QBasis, ∃ a b : Outcome → ℝ,
      U.matᴴ * A * U.mat = realDiagonal a ∧ U.matᴴ * B * U.mat = realDiagonal b := by
  obtain ⟨v, a, b, hn, ho, ha, hb⟩ := exists_orthonormal_joint_columns hA hB hAB
  let M := matrixOfColumns v
  have hM : Mᴴ * M = 1 := matrixOfColumns_adjoint_mul v hn ho
  let U : QBasis := ⟨M, hM, mul_adjoint_of_adjoint_mul M hM⟩
  exact ⟨U, a, b, adjoint_conjugate_eq_diagonal U A a (matrixOfColumns_eigenvectors A v a ha),
    adjoint_conjugate_eq_diagonal U B b (matrixOfColumns_eigenvectors B v b hb)⟩

end QuaternionicMUB
