module

public import ThirteenPlanes.Cartan.QuaternionRepresentation
public import ThirteenPlanes.Cartan.DiagonalWeights

@[expose] public section

set_option backward.privateInPublic true

/-! Conjugacy and frame type of the actual compact quaternionic Cartan subalgebras. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

/-- Maximal commutativity in the literal compact quaternionic operator algebra. -/
def IsQuaternionicOperatorCartan (T : Submodule ℝ quaternionOperatorAlgebra) : Prop :=
  (∀ A B : T, Commute A.val.val.val B.val.val.val) ∧
    ∀ D : quaternionOperatorAlgebra, (∀ H : T, Commute D.val.val H.val.val.val) → D ∈ T

private abbrev matrixOfQuatOp : quaternionOperatorAlgebra →ₗ[ℝ] QMat :=
  quaternionSkewMatrices.subtype.comp quaternionCommutatorEquiv.symm.toLinearMap

private theorem quaternionEquiv_symm_commutator (D : quaternionOperatorAlgebra) :
    quaternionCommutator (quaternionCommutatorEquiv.symm D) = D.val.val :=
  congrArg (fun E : quaternionOperatorAlgebra => E.val.val)
    (quaternionCommutatorEquiv.apply_symm_apply D)

/-- The displayed quaternionic diagonal torus is an actual Cartan subalgebra. -/
theorem quaternionStandardCartan_isCartan :
    IsQuaternionicOperatorCartan quaternionStandardCartan := by
  constructor
  · intro A B
    apply (quaternionJordan.restrictOperators_commute_iff quaternionOperatorAlgebra
      quaternionOperatorAlgebra_le A.val B.val).mp
    exact quaternionStandardFrameType.1
      ⟨quaternionRestrictOperators A.val, Submodule.mem_map_of_mem A.property⟩
      ⟨quaternionRestrictOperators B.val, Submodule.mem_map_of_mem B.property⟩
  · intro D hD
    let A := quaternionCommutatorEquiv.symm D
    have h (a : Fin 3 → ℝ) : Commute A.val (quaternionicStandardDiagonal a) := by
      apply (quaternionCommutator_commute_iff A (quaternionSkewDiagonal a)).mp
      rw [quaternionEquiv_symm_commutator]
      exact hD ⟨quaternionStandardFull a, ⟨a, rfl⟩⟩
    obtain ⟨a, ha⟩ := quaternionicStandardDiagonal_centralizer A.val A.property h
    have he : quaternionSkewDiagonal a = A := Subtype.ext ha
    exact ⟨a, (congrArg quaternionCommutatorEquiv he).trans
      (quaternionCommutatorEquiv.apply_symm_apply D)⟩

/-- Every maximal commutative quaternionic operator subspace is conjugate to the standard torus
by one actual quaternionic unitary. -/
/- This proves compact Cartan conjugacy in the quaternionic three-by-three matrix model
by simultaneous diagonalization. For the general compact conjugacy theorem cited in
the paper, see Anthony Knapp, Structure Theory of Semisimple Lie Groups (1997),
Theorem 3.6, p. 16. -/
theorem quaternionicOperatorCartan_conjugateStandard (T : Submodule ℝ quaternionOperatorAlgebra)
    (hT : IsQuaternionicOperatorCartan T) :
    ∃ U : QBasis, ((T.map quaternionRestrictOperators.toLinearMap).map
      (conjugateSkew ((quaternionJordanAction U).traceAction quaternionJordan)).toLinearMap) =
        quaternionStandardCartan.map quaternionRestrictOperators.toLinearMap := by
  let S := T.map matrixOfQuatOp
  have skew : ∀ A ∈ S, Aᴴ = -A := by
    rintro _ ⟨D, _, rfl⟩
    exact (quaternionCommutatorEquiv.symm D).property
  have comm : ∀ A ∈ S, ∀ B ∈ S, Commute A B := by
    rintro _ ⟨D, hD, rfl⟩ _ ⟨E, hE, rfl⟩
    apply (quaternionCommutator_commute_iff (quaternionCommutatorEquiv.symm D)
      (quaternionCommutatorEquiv.symm E)).mp
    rw [quaternionEquiv_symm_commutator, quaternionEquiv_symm_commutator]
    exact hT.1 ⟨D, hD⟩ ⟨E, hE⟩
  have max : ∀ X : QMat, Xᴴ = -X → (∀ Y ∈ S, Commute X Y) → X ∈ S := by
    intro X hX hx
    let A : quaternionSkewMatrices := ⟨X, hX⟩
    let D := quaternionCommutatorEquiv A
    have hD : D ∈ T := by
      apply hT.2
      intro H
      change Commute (quaternionCommutator A) H.val.val.val
      rw [← quaternionEquiv_symm_commutator H.val]
      apply (quaternionCommutator_commute_iff A (quaternionCommutatorEquiv.symm H.val)).mpr
      exact hx (matrixOfQuatOp H.val) (Submodule.mem_map_of_mem H.property)
    exact ⟨D, hD, congrArg Subtype.val (quaternionCommutatorEquiv.symm_apply_apply A)⟩
  obtain ⟨U, hU⟩ := quaternionicCartan_conjugateStandard S skew comm max
  let g := (quaternionJordanAction U).traceAction quaternionJordan
  have rep (D : quaternionOperatorAlgebra) :
      quaternionTraceRepresentation (quaternionCommutatorEquiv.symm D) =
        quaternionRestrictOperators D := by
    change quaternionRestrictOperators (quaternionCommutatorEquiv (quaternionCommutatorEquiv.symm D)) = _
    rw [quaternionCommutatorEquiv.apply_symm_apply]
  have std (a : Fin 3 → ℝ) : quaternionCommutatorEquiv (quaternionSkewDiagonal a) ∈
      quaternionStandardCartan := ⟨a, rfl⟩
  refine ⟨U, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨D, hD, rfl⟩, rfl⟩
    let A := quaternionCommutatorEquiv.symm D
    have hA : quaternionicPullback U A.val ∈ quaternionicStandardDiagonal.range := by
      rw [← hU]
      exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hD)
    obtain ⟨a, ha⟩ := hA
    have hB : quaternionSkewPullback U A = quaternionSkewDiagonal a := Subtype.ext ha.symm
    refine ⟨quaternionCommutatorEquiv (quaternionSkewDiagonal a), std a, ?_⟩
    have h1 := congrArg (conjugateSkew g) (rep D)
    have h2 := quaternionTraceRepresentation_conjugate U A
    have h3 := congrArg quaternionTraceRepresentation hB
    exact (h1.symm.trans (h2.trans h3)).symm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have hA : quaternionicStandardDiagonal a ∈ S.map (quaternionicPullback U).toLinearMap := by
      rw [hU]
      exact ⟨a, rfl⟩
    obtain ⟨_, ⟨D, hD, rfl⟩, hmain⟩ := hA
    let A := quaternionCommutatorEquiv.symm D
    refine ⟨quaternionRestrictOperators D, ⟨D, hD, rfl⟩, ?_⟩
    have hB : quaternionSkewPullback U A = quaternionSkewDiagonal a := Subtype.ext hmain
    have h1 := congrArg (conjugateSkew g) (rep D)
    have h2 := quaternionTraceRepresentation_conjugate U A
    have h3 := congrArg quaternionTraceRepresentation hB
    exact h1.symm.trans (h2.trans h3)

/-- Every compact quaternionic Cartan subalgebra is of frame type with constant one quarter. -/
theorem quaternionicOperatorCartan_frameType (T : Submodule ℝ quaternionOperatorAlgebra)
    (hT : IsQuaternionicOperatorCartan T) :
    IsFrameType (T.map quaternionRestrictOperators.toLinearMap) 3 (1 / 4) := by
  obtain ⟨U, hU⟩ := quaternionicOperatorCartan_conjugateStandard T hT
  let g := (quaternionJordanAction U).traceAction quaternionJordan
  have h := (conjugate_frameType_fixed g.symm _
    quaternionStandardFrameType).1
  rw [← hU, conjugateSkew_map_roundtrip] at h
  exact h

end

end ThirteenPlanes.Cartan
