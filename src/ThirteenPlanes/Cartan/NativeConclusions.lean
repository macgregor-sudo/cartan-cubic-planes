module

public import ThirteenPlanes.Cartan.AlbertOperators
public import ThirteenPlanes.Cartan.QuaternionFrames

@[expose] public section

/-! The fixed-plane and second-row conclusions on the actual native carriers. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace
open QuaternionicMUB

noncomputable section

theorem albertTraceFree_finrank : Module.finrank ℝ albertJordan.traceFree = 26 :=
  albertTraceEquiv.toLinearEquiv.finrank_eq.trans nativeTraceless_finrank

/-- Proposition 7.4(a) on the compact Albert representation. -/
theorem albert_fixedSubalgebra_and_framePlane
    (T : Submodule ℝ albertJordan.skewDerivations) :
    let A := T.map albertJordan.skewDerivations.subtype
    fixedSpace A = (ℝ ∙ albertJordan.unit) ⊔ (albertJordan.fixedTraceless A).map albertJordan.traceFree.subtype ∧
      albertJordan.unit ∈ fixedSpace A ∧
      (∀ x y, x ∈ fixedSpace A → y ∈ fixedSpace A → albertJordan.L x y ∈ fixedSpace A) ∧
      IsClosedPiece albertJordan.traceCubic (albertJordan.fixedTraceless A) ∧
      (Module.finrank ℝ (albertJordan.fixedTraceless A) = 2 →
        ∃ F : albertJordan.Frame, albertJordan.fixedTraceless A = F.plane albertJordan) := by
  apply albertJordan.fixedSubalgebra_and_framePlane albertJordan_closedPlane_has_frame
  rintro _ ⟨D, _, rfl⟩
  exact D.property

/-- Proposition 7.4(a) on the actual quaternionic commutator representation. -/
theorem quaternion_fixedSubalgebra_and_framePlane
    (T : Submodule ℝ quaternionOperatorAlgebra) :
    let A := T.map quaternionOperatorAlgebra.subtype
    fixedSpace A = (ℝ ∙ quaternionJordan.unit) ⊔ (quaternionJordan.fixedTraceless A).map quaternionJordan.traceFree.subtype ∧
      quaternionJordan.unit ∈ fixedSpace A ∧
      (∀ x y, x ∈ fixedSpace A → y ∈ fixedSpace A → quaternionJordan.L x y ∈ fixedSpace A) ∧
      IsClosedPiece quaternionJordan.traceCubic (quaternionJordan.fixedTraceless A) ∧
      (Module.finrank ℝ (quaternionJordan.fixedTraceless A) = 2 →
        ∃ F : quaternionJordan.Frame, quaternionJordan.fixedTraceless A = F.plane quaternionJordan) := by
  apply quaternionJordan.fixedSubalgebra_and_framePlane quaternion_closedPlane_has_frame
  rintro _ ⟨D, _, rfl⟩
  exact quaternionOperatorAlgebra_le D.property

/-- The thirteen fixed planes theorem on the compact Albert space of skew derivations. -/
theorem albert_frameTypeSplitting_fixedPlanes
    (T : Fin 13 → Submodule ℝ albertJordan.skewDerivations) (hT : OrthogonalSplit (E := albertJordan.skewDerivations) T)
    (hType : ∀ i, IsFrameType ((T i).map albertJordan.restrictDerivation) 4 (1 / 6)) :
    let U i := albertJordan.fixedTraceless ((T i).map albertJordan.skewDerivations.subtype)
    OrthogonalSplit (E := albertJordan.traceFree) U ∧
      (∀ i, IsClosedPiece albertJordan.traceCubic (U i)) ∧
      ∃ F : Fin 13 → albertJordan.Frame, (∀ i, U i = (F i).plane albertJordan) ∧
        (∀ i j, i ≠ j → ∀ a b, albertJordan.trace (albertJordan.L ((F i).point a) ((F j).point b)) = 1 / 3) :=
  albertJordan.operatorOD_fixedPlanes albertJordan.skewDerivations le_rfl T hT
    4 (1 / 6) (Module.finrank ℝ albertDerivationOperators / 26) (by norm_num)
    albertFullCasimir hType (by rw [albertTraceFree_finrank]; decide)
    albertJordan_closedPlane_has_frame

end

end ThirteenPlanes.Cartan
