module

public import ThirteenPlanes.Cartan.QuaternionFullCasimir
public import ThirteenPlanes.Cartan.QuaternionCartanOperators
public import ThirteenPlanes.Cartan.QuaternionFrames
public import ThirteenPlanes.Quaternionic.CapacityCorollaries

@[expose] public section

/-! The quaternionic fixed-plane theorem and compact orthogonal decomposition obstruction. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

/-- The seven fixed planes theorem on the quaternionic commutator representation. -/
theorem quaternion_frameTypeSplitting_fixedPlanes
    (T : Fin 7 → Submodule ℝ quaternionOperatorAlgebra) (hT : OrthogonalSplit (E := quaternionOperatorAlgebra) T)
    (hType : ∀ i, IsFrameType ((T i).map quaternionRestrictOperators.toLinearMap) 3 (1 / 4)) :
    let U i := quaternionJordan.fixedTraceless ((T i).map quaternionOperatorAlgebra.subtype)
    OrthogonalSplit (E := quaternionJordan.traceFree) U ∧
      (∀ i, IsClosedPiece quaternionJordan.traceCubic (U i)) ∧
      ∃ F : Fin 7 → quaternionJordan.Frame, (∀ i, U i = (F i).plane quaternionJordan) ∧
        (∀ i j, i ≠ j → ∀ a b,
          quaternionJordan.trace (quaternionJordan.L ((F i).point a) ((F j).point b)) = 1 / 3) :=
  quaternionJordan.operatorOD_fixedPlanes quaternionOperatorAlgebra quaternionOperatorAlgebra_le
    T hT 3 (1 / 4) (Module.finrank ℝ quaternionDerivationOperators / 14) (by norm_num)
    quaternionFullCasimir hType (by rw [quaternionTraceFree_finrank]; decide)
    quaternion_closedPlane_has_frame

/-- The native compact quaternionic operator decomposition is excluded by the seven-plane theorem. -/
theorem no_quaternionicOperatorOD :
    ¬ ∃ T : Fin 7 → Submodule ℝ quaternionOperatorAlgebra,
      OrthogonalSplit (E := quaternionOperatorAlgebra) T ∧ ∀ i, IsQuaternionicOperatorCartan (T i) := by
  rintro ⟨T, hT, hC⟩
  have hType (i : Fin 7) := quaternionicOperatorCartan_frameType (T i) (hC i)
  obtain ⟨hs, hclosed, _⟩ := quaternion_frameTypeSplitting_fixedPlanes T hT hType
  let P i := quaternionJordan.fixedTraceless ((T i).map quaternionOperatorAlgebra.subtype)
  let U i := (P i).map quaternionTraceEquiv.toLinearMap
  have hd (i : Fin 7) : Module.finrank ℝ (U i) = 2 := by
    have hq : Module.finrank ℝ (P i) = 2 := by
      change Module.finrank ℝ (quaternionJordan.fixedTraceless
        ((T i).map quaternionOperatorAlgebra.subtype)) = 2
      rw [quaternionJordan.fixedTraceless_eq_fixedSpace quaternionOperatorAlgebra quaternionOperatorAlgebra_le]
      exact (hType i).2.2.1
    exact (quaternionTraceEquiv.toLinearEquiv.submoduleMap (P i)).finrank_eq.symm.trans hq
  have ho : Pairwise fun i j => (U i).IsOrtho (U j) := by
    intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change ⟪quaternionTraceEquiv x, quaternionTraceEquiv y⟫ = 0
    have hInner : ⟪quaternionTraceEquiv x, quaternionTraceEquiv y⟫ = ⟪x, y⟫ := rfl
    exact hInner.trans ((hs.1 hij).inner_eq hx hy)
  apply no_seven_closedNativePlanes U hd ho
  intro i
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  change quaternionTraceCubic.L (quaternionTraceEquiv x) (quaternionTraceEquiv y) ∈ U i
  rw [← quaternion_traceCubic_map_L]
  exact Submodule.mem_map_of_mem (hclosed i hx hy)


end

end ThirteenPlanes.Cartan
