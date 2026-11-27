module

public import ThirteenPlanes.Quaternionic.QuaternionLine
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! Quaternionic spectral theory through real joint eigenspaces.

The real joint-eigenspace theorem is applied on invariant subspaces. Right quaternion stability
allows the resulting eigenvectors to be assembled into a native unitary basis. -/

noncomputable section

open scoped BigOperators Matrix
open Module.End

namespace QuaternionicMUB

/-- A commuting native Hermitian pair has a nonzero common eigenvector in every
nonzero invariant real subspace. Eigenvalue multiplicities are unrestricted. -/
lemma exists_joint_eigenvector_on {A B : QMat}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B)
    (S : Submodule ℝ QHilbert) (hS : S ≠ ⊥)
    (hAS : ∀ v ∈ S, realAction A v ∈ S)
    (hBS : ∀ v ∈ S, realAction B v ∈ S) :
    ∃ v : QHilbert, v ∈ S ∧ v ≠ 0 ∧ ∃ a b : ℝ,
      realAction A v = a • v ∧ realAction B v = b • v := by
  classical
  let : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS
  let LA : S →ₗ[ℝ] S := (realAction A).restrict hAS
  let LB : S →ₗ[ℝ] S := (realAction B).restrict hBS
  have hLA : LA.IsSymmetric := (realAction_isSymmetric hA).restrict_invariant hAS
  have hLB : LB.IsSymmetric := (realAction_isSymmetric hB).restrict_invariant hBS
  have hLAB : Commute LA LB := LinearMap.restrict_commute (realAction_commute hAB) hAS hBS
  have htop := hLA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hLB hLAB
  have hex : ∃ a b : ℝ, eigenspace LA a ⊓ eigenspace LB b ≠ ⊥ := by
    by_contra h
    have hz (a b : ℝ) : eigenspace LA a ⊓ eigenspace LB b = ⊥ := by
      by_contra hn
      exact h ⟨a, b, hn⟩
    have ht : (⊤ : Submodule ℝ S) = ⊥ := by
      simpa only [hz, iSup_bot] using htop.symm
    exact top_ne_bot ht
  obtain ⟨a, b, hab⟩ := hex
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hab
  refine ⟨v, v.property, ?_, a, b, ?_, ?_⟩
  · intro h
    exact hv0 (Subtype.ext h)
  · exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv.1)
  · exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv.2)

end QuaternionicMUB
