module

public import ThirteenPlanes.Cartan.Restriction

@[expose] public section

/-! Conjugation of the actual traceless representation by unital Jordan isometries. -/

namespace ThirteenPlanes.Cartan

open scoped RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

namespace TraceJordanData

variable (M : TraceJordanData J)

/-- A unital Jordan automorphism preserving the trace metric. -/
structure Automorphism where
  action : J ≃ₗᵢ[ℝ] J
  unit_fixed : action M.unit = M.unit
  product_map : ∀ x y, action (M.L x y) = M.L (action x) (action y)

def Automorphism.symm (g : M.Automorphism) : M.Automorphism where
  action := g.action.symm
  unit_fixed := g.action.symm_apply_eq.mpr g.unit_fixed.symm
  product_map x y := by
    apply g.action.injective
    rw [g.action.apply_symm_apply, g.product_map,
      g.action.apply_symm_apply, g.action.apply_symm_apply]

omit [FiniteDimensional ℝ J] in
theorem Automorphism.trace_map (g : M.Automorphism) (x : J) :
    M.trace (g.action x) = M.trace x := by
  change ⟪M.unit, g.action x⟫ = ⟪M.unit, x⟫
  rw [← g.action.inner_map_map M.unit x, g.unit_fixed]

/-- The induced isometric action on the traceless Jordan representation. -/
def Automorphism.traceAction (g : M.Automorphism) : M.traceFree ≃ₗᵢ[ℝ] M.traceFree where
  toFun x := ⟨g.action x.val, (g.trace_map M x.val).trans x.property⟩
  invFun x := ⟨g.action.symm x.val, ((g.symm M).trace_map M x.val).trans x.property⟩
  left_inv x := Subtype.ext (g.action.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.action.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (g.action.map_add x.val y.val)
  map_smul' r x := Subtype.ext (g.action.map_smul r x.val)
  norm_map' x := g.action.norm_map x.val

theorem Automorphism.conjugate_mem_skewDerivations (g : M.Automorphism)
    (D : M.skewDerivations) : conjugateSkew g.action D.val ∈ M.skewDerivations := by
  intro x y
  change g.action (D.val.val (g.action.symm (M.L x y))) =
    M.L (g.action (D.val.val (g.action.symm x))) y +
      M.L x (g.action (D.val.val (g.action.symm y)))
  have hxy : g.action.symm (M.L x y) = M.L (g.action.symm x) (g.action.symm y) :=
    (g.symm M).product_map x y
  rw [hxy, D.property, map_add, g.product_map, g.product_map, g.action.apply_symm_apply,
    g.action.apply_symm_apply]

def Automorphism.conjugateDerivation (g : M.Automorphism) (D : M.skewDerivations) :
    M.skewDerivations :=
  ⟨conjugateSkew g.action D.val, g.conjugate_mem_skewDerivations M D⟩

theorem Automorphism.conjugate_restrictDerivation (g : M.Automorphism) (D : M.skewDerivations) :
    conjugateSkew (g.traceAction M) (M.restrictDerivation D) =
      M.restrictDerivation (g.conjugateDerivation M D) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem Automorphism.normalizes_restrictedDerivations (g : M.Automorphism) :
    (LinearMap.range M.restrictDerivation).map (conjugateSkew (g.traceAction M)).toLinearMap =
      LinearMap.range M.restrictDerivation := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨D, rfl⟩, rfl⟩
    exact ⟨g.conjugateDerivation M D, (g.conjugate_restrictDerivation M D).symm⟩
  · rintro _ ⟨D, rfl⟩
    refine ⟨M.restrictDerivation ((g.symm M).conjugateDerivation M D), ⟨_, rfl⟩, ?_⟩
    change conjugateSkew (g.traceAction M)
      (M.restrictDerivation ((g.symm M).conjugateDerivation M D)) = M.restrictDerivation D
    rw [g.conjugate_restrictDerivation]
    apply congrArg M.restrictDerivation
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change g.action (g.action.symm (D.val.val (g.action (g.action.symm x)))) = D.val.val x
    rw [g.action.apply_symm_apply, g.action.apply_symm_apply]

omit [FiniteDimensional ℝ J] in
theorem Automorphism.leftMul_conjugate (g : M.Automorphism) (x : J) :
    M.L (g.action x) = g.action.toLinearEquiv.conj (M.L x) := by
  apply LinearMap.ext
  intro y
  change M.L (g.action x) y = g.action (M.L x (g.action.symm y))
  rw [g.product_map, g.action.apply_symm_apply]

end TraceJordanData

end

end ThirteenPlanes.Cartan
