module

public import ThirteenPlanes.Cartan.ClassicalQuaternionicKilling
public import ThirteenPlanes.Cartan.QuaternionOD

@[expose] public section

/-! The compact symplectic obstruction with literal Lie Cartans and Killing orthogonality. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB LieAlgebra
open scoped RealInnerProductSpace

noncomputable section

/-- The faithful commutator representation identifies the two compact Cartan predicates. -/
theorem compactSp3_cartan_iff_operatorCartan (T : LieSubalgebra ℝ compactSp3) :
    T.IsCartanSubalgebra ↔
      IsQuaternionicOperatorCartan (T.toSubmodule.map compactSp3Operators.toLinearMap) := by
  rw [← compactCartan_iff_cartan compactSp3_compactKilling]
  let f := compactSp3Operators
  let S := T.toSubmodule.map f.toLinearMap
  have hmem (A : compactSp3) : f A ∈ S ↔ A ∈ T := by
    constructor
    · rintro ⟨B, hB, he⟩
      exact (f.injective he) ▸ hB
    · exact Submodule.mem_map_of_mem
  have hcomm (A B : compactSp3) :
      Commute (f A).val.val (f B).val.val ↔ ⁅A,B⁆ = 0 := by
    rw [show Commute (f A).val.val (f B).val.val ↔ Commute A.val B.val
      from quaternionCommutator_commute_iff A B]
    exact ⟨fun h => Subtype.ext (sub_eq_zero.mpr h.eq),
      fun h => sub_eq_zero.mp (congrArg Subtype.val h)⟩
  constructor
  · intro hT
    refine ⟨?_, ?_⟩
    · rintro ⟨_, A, hA, rfl⟩ ⟨_, B, hB, rfl⟩
      exact (hcomm A B).mpr ((hT A).2 hA B hB)
    · intro D hD
      obtain ⟨A,rfl⟩ := f.surjective D
      apply (hmem A).mpr
      apply (hT A).1
      intro B hB
      exact (hcomm A B).mp (hD ⟨f B, (hmem B).mpr hB⟩)
  · intro hT A
    constructor
    · intro hA
      apply (hmem A).mp
      apply hT.2
      rintro ⟨_, B, hB, rfl⟩
      exact (hcomm A B).mpr (hA B hB)
    · intro hA B hB
      exact (hcomm A B).mp (hT.1 ⟨f A, (hmem A).mpr hA⟩ ⟨f B, (hmem B).mpr hB⟩)

/-- Every compact symplectic Cartan acts on the actual trace-zero Hermitian matrices
with the two-dimensional fixed space and the Casimir constant one quarter. -/
theorem compactSp3_cartan_frameType (T : LieSubalgebra ℝ compactSp3)
    (hT : T.IsCartanSubalgebra) :
    IsFrameType (T.toSubmodule.map compactSp3TraceRepresentation) 3 (1 / 4) := by
  have h := quaternionicOperatorCartan_frameType _ ((compactSp3_cartan_iff_operatorCartan T).mp hT)
  change IsFrameType (T.toSubmodule.map
    (quaternionRestrictOperators.toLinearMap.comp compactSp3Operators.toLinearMap)) 3 (1 / 4)
  rw [Submodule.map_comp]
  exact h

/-- The compact symplectic obstruction. The algebra of skew-Hermitian quaternionic three-by-three matrices
has no complete Killing-orthogonal decomposition into Cartan subalgebras. -/
theorem no_compactSp3_cartanOD {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ¬ ∃ T : ι → LieSubalgebra ℝ compactSp3, IsKillingCartanOD T := by
  rintro ⟨T, hT⟩
  let e : Fin 7 ≃ ι := (Fintype.equivFinOfCardEq (compactSp3_cartanOD_card T hT)).symm
  let f := compactSp3Operators
  let S (i : Fin 7) := (T (e i)).toSubmodule.map f.toLinearMap
  have horth : Pairwise (fun i j : Fin 7 =>
      Submodule.IsOrtho (𝕜 := ℝ) (E := quaternionOperatorAlgebra) (S i) (S j)) := by
    intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    have hz := hT.2.1 (fun h => hij (e.injective h)) A hA B hB
    rw [compactSp3_killing_trace_ratio] at hz
    have hzero : ⟪compactSp3TraceRepresentation A, compactSp3TraceRepresentation B⟫ = 0 :=
      (mul_eq_zero.mp hz).resolve_left (by norm_num)
    exact ((quaternionRestrictOperators.inner_map_map (f A) (f B)).symm).trans hzero
  have hreindex : (⨆ i : Fin 7, (T (e i)).toSubmodule) = ⨆ j : ι, (T j).toSubmodule :=
    e.surjective.iSup_comp (fun j => (T j).toSubmodule)
  have hspan : iSup S = ⊤ := by
    change (⨆ i : Fin 7, (T (e i)).toSubmodule.map f.toLinearMap) = ⊤
    rw [← Submodule.map_iSup, hreindex, hT.2.2.submodule_iSup_eq_top,
      Submodule.map_top, LinearMap.range_eq_top.mpr f.surjective]
  have hi0 : iSupIndep (fun i : Fin 7 => (T (e i)).toSubmodule) :=
    hT.2.2.submodule_iSupIndep.comp e.injective
  have hi : iSupIndep S := f.toLinearMap.iSupIndep_map f.injective hi0
  have hsplit : OrthogonalSplit (E := quaternionOperatorAlgebra) S :=
    ⟨horth, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi hspan⟩
  have hCartan (i : Fin 7) : IsQuaternionicOperatorCartan (S i) :=
    (compactSp3_cartan_iff_operatorCartan (T (e i))).mp (hT.1 (e i))
  exact no_quaternionicOperatorOD ⟨S, hsplit, hCartan⟩

end
end ThirteenPlanes.Cartan
