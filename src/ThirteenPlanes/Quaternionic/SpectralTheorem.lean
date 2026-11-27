module

public import ThirteenPlanes.Quaternionic.FrameDictionary
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true

/-! Quaternionic spectral bases on every right-invariant subspace. -/

open scoped BigOperators Matrix InnerProductSpace

namespace QuaternionicMUB

/-- A finite right quaternionic orthonormal basis of an actual right subspace.
The supremum of the right lines is the span with quaternionic coefficients. -/
structure RightOrthonormalBasis (S : Submodule ℝ QHilbert) where
  count : ℕ
  vector : Fin count → QHilbert
  mem : ∀ i, vector i ∈ S
  norm_eq_one : ∀ i, ‖vector i‖ = 1
  orthogonal : ∀ i j, i ≠ j → qInner (columnEquiv (vector i)) (columnEquiv (vector j)) = 0
  spans : (⨆ i, rightLine (vector i)) = S

/-- Every right-invariant subspace of a native Hermitian matrix has an
orthonormal basis of real eigenvectors, with no restriction on multiplicities. -/
/- The quaternionic Hermitian spectral theorem is discussed by Fuzhen Zhang (1997) and
Leiba Rodman (2014, Theorem 5.3.6, as cited in arXiv:2012.03621, §3.1). The proof
splits off the right quaternionic line of a unit real eigenvector of the associated real
self-adjoint operator and continues on its orthogonal complement. -/
theorem rightInvariant_has_eigenbasis (A : QMat) (hA : A.IsHermitian)
    (S : Submodule ℝ QHilbert) (hS : RightStable S)
    (hAS : ∀ v ∈ S, realAction A v ∈ S) :
    ∃ E : RightOrthonormalBasis S, ∃ a : Fin E.count → ℝ,
      ∀ i, realAction A (E.vector i) = a i • E.vector i := by
  classical
  have build (n : ℕ) : ∀ T : Submodule ℝ QHilbert, Module.finrank ℝ T = n →
      RightStable T → (∀ v ∈ T, realAction A v ∈ T) →
      ∃ E : RightOrthonormalBasis T, ∃ a : Fin E.count → ℝ,
        ∀ i, realAction A (E.vector i) = a i • E.vector i := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro T hn hT hAT
      by_cases hbot : T = ⊥
      · let E : RightOrthonormalBasis T :=
          ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
            fun i => Fin.elim0 i, by simp [hbot]⟩
        exact ⟨E, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
      obtain ⟨v, hv, hvunit, a, _, hva, _⟩ := exists_unit_joint_eigenvector_on
        hA hA (Commute.refl A) T hbot hAT hAT
      have hvzero : v ≠ 0 := by
        intro h
        simp [h] at hvunit
      let K := (rightLine v)ᗮ ⊓ T
      have hline : rightLine v ≤ T := rightLine_le hT hv
      have hdim : Module.finrank ℝ K < n := by
        have hsum : Module.finrank ℝ (rightLine v) + Module.finrank ℝ K =
            Module.finrank ℝ T := Submodule.finrank_add_inf_finrank_orthogonal hline
        rw [finrank_rightLine hvzero, hn] at hsum
        omega
      have hK : RightStable K := rightStable_inf (rightStable_rightLine_orthogonal v) hT
      have hAK : ∀ w ∈ K, realAction A w ∈ K := fun w hw =>
        ⟨rightLine_orthogonal_invariant hA hva w hw.1, hAT w hw.2⟩
      obtain ⟨E, b, hb⟩ := ih _ hdim K rfl hK hAK
      let u : Fin (E.count + 1) → QHilbert := Fin.cons v E.vector
      let d : Fin (E.count + 1) → ℝ := Fin.cons a b
      have hu0 : u 0 = v := by simp [u]
      have hus (i : Fin E.count) : u i.succ = E.vector i := by simp [u]
      have hu_ortho (i : Fin E.count) :
          qInner (columnEquiv v) (columnEquiv (E.vector i)) = 0 :=
        (mem_rightLine_orthogonal_iff v _).mp (E.mem i).1
      refine ⟨⟨E.count + 1, u, ?_, ?_, ?_, ?_⟩, d, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hu0.symm ▸ hv
        · exact (hus j).symm ▸ (E.mem j).2
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hu0.symm ▸ hvunit
        · exact (hus j).symm ▸ E.norm_eq_one j
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · intro j
          refine Fin.cases (fun hn => (hn rfl).elim) (fun j _ => ?_) j
          rw [hu0, hus]
          exact hu_ortho j
        · intro j
          refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j
          · rw [hu0, hus, qInner_star (columnEquiv v), hu_ortho, star_zero]
          · rw [hus, hus]
            exact E.orthogonal i j (fun h => hij (congrArg Fin.succ h))
      · have hspan : (⨆ i, rightLine (u i)) = rightLine v ⊔ (⨆ i, rightLine (E.vector i)) := by
          apply le_antisymm
          · refine iSup_le fun i => ?_
            refine Fin.cases ?_ (fun j => ?_) i
            · rw [hu0]
              exact le_sup_left
            · rw [hus]
              exact (le_iSup (fun i => rightLine (E.vector i)) j).trans le_sup_right
          · refine sup_le ?_ (iSup_le fun j => ?_)
            · rw [← hu0]
              exact le_iSup (fun i => rightLine (u i)) 0
            · rw [← hus j]
              exact le_iSup (fun i => rightLine (u i)) j.succ
        rw [hspan, E.spans]
        exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hline
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [hu0, d, Fin.cons_zero] using hva
        · simpa only [hus, d, Fin.cons_succ] using hb j
  exact build _ S rfl hS hAS

private theorem matrix_eigen_eq_of_diagonalization (U : QBasis) (A : QMat) (a : Outcome → ℝ)
    (ha : U.matᴴ * A * U.mat = realDiagonal a) : A * U.mat = U.mat * realDiagonal a := by
  calc
    A * U.mat = (U.mat * U.matᴴ) * A * U.mat := by rw [U.mul_adjoint, one_mul]
    _ = U.mat * (U.matᴴ * A * U.mat) := by simp only [mul_assoc]
    _ = _ := by rw [ha]

/-- A commuting pair has a common actual unitary eigenbasis with real eigenvalues. -/
theorem simultaneous_eigenbasis (A B : QMat) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U : QBasis, ∃ a b : Outcome → ℝ,
      A * U.mat = U.mat * realDiagonal a ∧ B * U.mat = U.mat * realDiagonal b := by
  obtain ⟨U, a, b, ha, hb⟩ := commuting_hermitian_simultaneous_diagonalization A B hA hB hAB
  exact ⟨U, a, b, matrix_eigen_eq_of_diagonalization U A a ha,
    matrix_eigen_eq_of_diagonalization U B b hb⟩

/-- The native outer-product expansion from a whole-space Hermitian eigenbasis. -/
theorem hermitian_projector_expansion (A : QMat) (hA : A.IsHermitian) :
    ∃ U : QBasis, ∃ a : Outcome → ℝ,
      A * U.mat = U.mat * realDiagonal a ∧ A = ∑ i, a i • U.point i := by
  obtain ⟨U, a, _, ha, _⟩ := simultaneous_eigenbasis A A hA hA (Commute.refl A)
  refine ⟨U, a, ha, ?_⟩
  calc
    A = (A * U.mat) * U.matᴴ := by rw [mul_assoc, U.mul_adjoint, mul_one]
    _ = (U.mat * realDiagonal a) * U.matᴴ := by rw [ha]
    _ = ∑ i, a i • U.point i := by
      apply Matrix.ext
      intro j k
      rw [Matrix.mul_apply, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [realDiagonal, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Quaternion.mul_coe_eq_smul]
      change (a i • U.mat j i) * star (U.mat k i) =
        a i • (U.mat j i * star (U.mat k i))
      rw [smul_mul_assoc]

/-- All three clauses of the native quaternionic spectral theorem. -/
theorem spectralTheorem :
    (∀ (A : QMat), A.IsHermitian → ∀ S : Submodule ℝ QHilbert, RightStable S →
      (∀ v ∈ S, realAction A v ∈ S) →
      ∃ E : RightOrthonormalBasis S, ∃ a : Fin E.count → ℝ,
        ∀ i, realAction A (E.vector i) = a i • E.vector i) ∧
    (∀ (A : QMat), A.IsHermitian →
      ∃ U : QBasis, ∃ a : Outcome → ℝ,
        A * U.mat = U.mat * realDiagonal a ∧ A = ∑ i, a i • U.point i) ∧
    (∀ (A B : QMat), A.IsHermitian → B.IsHermitian → Commute A B →
      ∃ U : QBasis, ∃ a b : Outcome → ℝ,
        A * U.mat = U.mat * realDiagonal a ∧ B * U.mat = U.mat * realDiagonal b) ∧
    (∀ F : Frame, ∃ U : QBasis, ∀ i, U.point i = F.point i) :=
  ⟨rightInvariant_has_eigenbasis, hermitian_projector_expansion,
    simultaneous_eigenbasis, frame_has_basis⟩

end QuaternionicMUB
