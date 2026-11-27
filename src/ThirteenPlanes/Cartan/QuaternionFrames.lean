module

public import ThirteenPlanes.Cartan.QuaternionJordan
public import ThirteenPlanes.Quaternionic.ClosedFramePlanes

@[expose] public section

/-! The closed frame planes of the quaternionic Jordan operator model. -/

namespace ThirteenPlanes.Cartan

open scoped Matrix BigOperators RealInnerProductSpace
open QuaternionicMUB

noncomputable section

theorem quaternion_traceCubic_map_L (x y : quaternionJordan.traceFree) :
    quaternionTraceEquiv (quaternionJordan.traceCubic.L x y) =
      quaternionTraceCubic.L (quaternionTraceEquiv x) (quaternionTraceEquiv y) := by
  have hcenter (z : HermitianHilbert) :
      fullMat (quaternionJordan.center z).val = centerMatrix (fullMat z) := by
    change fullMat (z - (quaternionJordan.trace z / 3) • fullUnit) = _
    rw [map_sub, map_smul, fullMat_fullUnit, quaternionJordan_trace]
    rfl
  have hprod : fullMat (quaternionJordan.L x.val y.val) = jordan (fullMat x.val) (fullMat y.val) :=
    quaternion_L_matrix x.val y.val
  have hleft : fullMat (quaternionJordan.traceCubic.L x y).val =
      centerMatrix (jordan (fullMat x.val) (fullMat y.val)) :=
    (congrArg (fun z : quaternionJordan.traceFree => fullMat z.val)
      (quaternionJordan.traceCubic_L x y)).trans
      ((hcenter _).trans (congrArg centerMatrix hprod))
  have hright := quaternionTraceCubic_L_matrix (quaternionTraceEquiv x) (quaternionTraceEquiv y)
  simp only [quaternionTraceEquiv_matrix] at hright
  exact traceMat_injective ((quaternionTraceEquiv_matrix _).trans (hleft.trans hright.symm))

/-- Lift an actual quaternionic Jordan frame into the unital trace-metric representation. -/
def quaternionJordanFrame (F : QuaternionicMUB.Frame) : quaternionJordan.Frame where
  point a := fullOfMatrix (F.point a) (F.hermitian a)
  trace_one a := by rw [quaternionJordan_trace, fullMat_ofMatrix, F.trace_one]
  mul_point a b := by
    apply fullMat_injective
    change fullMat (quaternionFullCubic.L _ _) = _
    rw [quaternion_L_matrix, fullMat_ofMatrix, fullMat_ofMatrix]
    split_ifs with hab
    · subst b
      rw [fullMat_ofMatrix, F.idempotent]
    · rw [map_zero, F.orthogonal a b hab]
  sum_unit := by
    apply fullMat_injective
    change fullMat (∑ a, fullOfMatrix (F.point a) (F.hermitian a)) = fullMat fullUnit
    rw [map_sum, fullMat_fullUnit]
    simpa only [fullMat_ofMatrix] using F.sum_points

/-- The frame span constructed in the unital model has exactly the native centered points. -/
theorem quaternionJordanFrame_plane (F : QuaternionicMUB.Frame) :
    ((quaternionJordanFrame F).plane quaternionJordan).map quaternionTraceEquiv.toLinearMap =
      F.centeredPlane := by
  rw [TraceJordanData.Frame.plane, Submodule.map_span, ← Set.range_comp]
  change Submodule.span ℝ (Set.range fun a =>
    quaternionTraceEquiv (quaternionJordan.center ((quaternionJordanFrame F).point a))) = _
  have h (a : Fin 3) :
      quaternionTraceEquiv (quaternionJordan.center ((quaternionJordanFrame F).point a)) =
        F.centeredHilbert a := by
    apply traceMat_injective
    rw [traceMat_centeredHilbert]
    change fullMat ((quaternionJordan.center ((quaternionJordanFrame F).point a)).val) = _
    change fullMat ((quaternionJordanFrame F).point a -
      (quaternionJordan.trace ((quaternionJordanFrame F).point a) / 3) • fullUnit) = _
    rw [map_sub, map_smul, (quaternionJordanFrame F).trace_one, fullMat_fullUnit]
    simp only [quaternionJordanFrame, fullMat_ofMatrix, QuaternionicMUB.Frame.centeredPointMatrix]
  simp_rw [h]
  rfl

/-- Every closed two-plane of the native quaternionic operator model comes from a frame. -/
theorem quaternion_closedPlane_has_frame (U : Submodule ℝ quaternionJordan.traceFree)
    (hd : Module.finrank ℝ U = 2) (hc : IsClosedPiece quaternionJordan.traceCubic U) :
    ∃ F : quaternionJordan.Frame, U = F.plane quaternionJordan := by
  let W := U.map quaternionTraceEquiv.toLinearMap
  have hdW : Module.finrank ℝ W = 2 :=
    (quaternionTraceEquiv.toLinearEquiv.submoduleMap U).finrank_eq.symm.trans hd
  have hcW : IsClosedPiece quaternionTraceCubic W := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    change quaternionTraceCubic.L (quaternionTraceEquiv x) (quaternionTraceEquiv y) ∈ W
    rw [← quaternion_traceCubic_map_L]
    exact Submodule.mem_map_of_mem (hc hx hy)
  obtain ⟨F, hF⟩ := QuaternionicMUB.closedPlane_has_frame W hdW hcW
  refine ⟨quaternionJordanFrame F, ?_⟩
  apply Submodule.map_injective_of_injective quaternionTraceEquiv.injective
  rw [quaternionJordanFrame_plane]
  exact hF

end

end ThirteenPlanes.Cartan
