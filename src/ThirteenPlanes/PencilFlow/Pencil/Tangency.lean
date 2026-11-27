module

public import ThirteenPlanes.PencilFlow.Pencil.Contractions

@[expose] public section

/-! The one-loop invariance of the pencil, tangency: on the intrinsic pencil, the tensor one-loop
field is the pencil image of the physical coefficient field. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.PencilFlow.Pencil

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem apply_sub_cubic (h g : SymmetricCubic V) (x y z : V) :
    (h - g).apply x y z = h.apply x y z - g.apply x y z := by
  simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]

/-- The one-loop field restricted to the pencil of a closed round plane system. -/
theorem closedPencil_tangent {m : ℕ} (h : SymmetricCubic V) (c : ℝ)
    (planes : PlaneDecomposition V (Fin m)) (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) (ε : ℝ) (u : ℝ × ℝ) :
    oneLoopBeta ε (coupling (planePencil h planes) u) =
      coupling (planePencil h planes)
        (Statements.physicalCoefficientField c (Statements.pencilLambda V) ε u) := by
  rcases u with ⟨a, b⟩
  obtain ⟨hM, hT⟩ := closedPencil_contractions h c planes round closed a b
  simp only [oneLoopBeta, hM, hT, insert_smul_id]
  apply SymmetricCubic.ext
  intro x y z
  simp only [coupling_apply, Statements.physicalCoefficientField, flowScale, apply_smul,
    apply_sub_cubic, apply_add]
  field_simp
  ring

end

end ThirteenPlanes.PencilFlow.Pencil
