module

public import ThirteenPlanes.Cartan.SecondRowSplitting
public import ThirteenPlanes.Cartan.LeftMulInvariant

@[expose] public section

/-! Derive the second-row conclusions from the proved frame and invariant-operator statements. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

/-- Proposition 7.9(a) with the dimension-two premise on the actual fixed plane. -/
theorem secondRow_centralizer_of_fixedDimension (M : TraceJordanData J)
    (K : Submodule ℝ (SkewOperator J)) (hK : K ≤ M.skewDerivations) (T : Submodule ℝ K)
    (hT : ∀ A B : T, Commute A.val.val.val B.val.val.val)
    (hMax : ∀ D : K, (∀ H : T, operatorBracket H.val.val.val D.val.val = 0) ↔ D ∈ T)
    (frames : ∀ U : Submodule ℝ M.traceFree, Module.finrank ℝ U = 2 →
      IsClosedPiece M.traceCubic U → ∃ F : M.Frame, U = F.plane M)
    (hDim : Module.finrank ℝ (representedFixedPlane M T) = 2) :
    (∀ X : secondRowSpace M K,
      (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0) ↔
        X ∈ secondRowPieceInSpace M T) ∧
    (∀ X Y, X ∈ secondRowPiece M T → Y ∈ secondRowPiece M T → Commute X Y) ∧
    (secondRowPieceInSpace M T).map (secondRowTheta M K).toLinearMap =
      secondRowPieceInSpace M T ∧
    (∀ B : Submodule ℝ (secondRowSpace M K),
      (∀ X Y : B, Commute X.val.val Y.val.val) →
      (∀ H : T, secondRowCoordinates M K (H.val, 0) ∈ B) →
      B ≤ secondRowPieceInSpace M T) := by
  have hder : T.map K.subtype ≤ M.skewDerivations := by
    rintro _ ⟨D, _, rfl⟩
    exact hK D.property
  obtain ⟨F, hF⟩ := (M.fixedSubalgebra_and_framePlane frames _ hder).2.2.2.2 hDim
  exact secondRow_operatorCentralizer M K hK T hT hMax F hF

/-- Proposition 7.9(b) using the actual trace-normalized Casimirs and a scalar commutant. -/
theorem secondRow_of_frameTypeSplitting {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) (hK : K ≤ M.skewDerivations)
    (T : ι → Submodule ℝ K) (hT : OrthogonalSplit T)
    (rank : ℕ) (κ scalar : ℝ) (hκ : 0 < κ)
    (hFull : operatorCasimir (LinearMap.range (M.restrictOperators K hK).toLinearMap) =
      scalar • LinearMap.id)
    (hType : ∀ i, IsFrameType ((T i).map (M.restrictOperators K hK).toLinearMap) rank κ)
    (hCard : 2 * Fintype.card ι = Module.finrank ℝ M.traceFree)
    (frames : ∀ U : Submodule ℝ M.traceFree, Module.finrank ℝ U = 2 →
      IsClosedPiece M.traceCubic U → ∃ F : M.Frame, U = F.plane M)
    {G : Type*} (act : G → M.Automorphism)
    (commutant : ∀ S : Module.End ℝ M.traceFree,
      (∀ g x, S ((act g).traceAction M x) = (act g).traceAction M (S x)) →
        ∃ a : ℝ, S = a • LinearMap.id) :
    SecondRowSplitting M T rank := by
  obtain ⟨hu, _, F, hF, _⟩ :=
    M.operatorOD_fixedPlanes K hK T hT rank κ scalar hκ hFull hType hCard frames
  obtain ⟨c, hc⟩ := leftMul_trace_eq_inner M act commutant
  let f := M.restrictOperators K hK
  have hRank (i : ι) : Module.finrank ℝ (T i) = rank := by
    let L := f.toLinearMap.comp (T i).subtype
    have hL : Function.Injective L := f.injective.comp Subtype.val_injective
    have hR : LinearMap.range L = (T i).map f.toLinearMap := by
      simp only [L, LinearMap.range_comp, Submodule.range_subtype]
    rw [← LinearMap.finrank_range_of_inj hL, hR]
    exact (hType i).2.1
  have hDim (i : ι) : Module.finrank ℝ (representedFixedPlane M (T i)) = 2 := by
    change Module.finrank ℝ (M.fixedTraceless ((T i).map K.subtype)) = 2
    rw [M.fixedTraceless_eq_fixedSpace K hK]
    exact (hType i).2.2.1
  have hComm (i : ι) (A B : T i) : Commute A.val.val.val B.val.val.val := by
    apply (M.restrictOperators_commute_iff K hK A.val B.val).mp
    exact (hType i).1 ⟨f A.val, Submodule.mem_map_of_mem A.property⟩
      ⟨f B.val, Submodule.mem_map_of_mem B.property⟩
  exact secondRow_operatorOD M K hK T hT hu rank hRank hDim hComm F hF c hc

end

end ThirteenPlanes.Cartan
