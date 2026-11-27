module

public import ThirteenPlanes.Cartan.JordanAction
public import ThirteenPlanes.PencilFlow.Hessian.Stabilizer
public import ThirteenPlanes.Peirce.SlotClosedPlaneIdentification

@[expose] public section

/-! The operator exponential of a real trace-skew derivation of a unital Jordan algebra. -/

namespace ThirteenPlanes.Cartan.TraceJordanData

open scoped RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
  (M : TraceJordanData J)

/-- The exponential of a trace-skew derivation preserves the full Jordan product and the unit. -/
def expAutomorphism (D : M.skewDerivations) : M.Automorphism := by
  let C := SymmetricCubic.ofProduct M.L M.comm (fun x y z =>
    (M.assoc_inner x y z).trans (real_inner_comm (M.L x z) y))
  let Ω : skewEnd J := ⟨D.val.val, mem_skewEnd.mpr D.val.property⟩
  let F := skewRotation D.val.val D.val.property
  have hC : Ω ∈ skewStabilizer C := by
    rw [mem_skewStabilizer]
    apply SymmetricCubic.ext
    intro x y z
    rw [SymmetricCubic.apply_insert, SymmetricCubic.apply_zero]
    change ⟪M.L (D.val.val x) y, z⟫ + ⟪M.L x (D.val.val y), z⟫ + ⟪M.L x y, D.val.val z⟫ = 0
    rw [← inner_add_left, ← D.property x y, D.val.property]
    abel
  have hF : C.pullback F.toLinearMap = C := by
    have he := (PencilFlow.HessianBridge.mem_skewStabilizer_iff_rotation C Ω).mp hC 1
    simpa only [one_smul] using he
  have mul (x y : J) : F (M.L x y) = M.L (F x) (F y) :=
    Peirce.pullback_intertwines_product F hF.symm x y (h := C) (k := C)
  refine ⟨F, ?_, mul⟩
  calc
    F M.unit = M.L (F M.unit) M.unit := (M.L_unit_right _).symm
    _ = M.L (F M.unit) (F (F.symm M.unit)) := by rw [F.apply_symm_apply]
    _ = F (M.L M.unit (F.symm M.unit)) := (mul _ _).symm
    _ = M.unit := by rw [M.unit_left, F.apply_symm_apply]

theorem expAutomorphism_apply (D : M.skewDerivations) (x : J) :
    (M.expAutomorphism D).action x =
      NormedSpace.exp (LinearMap.toContinuousLinearMap D.val.val) x := rfl

end

end ThirteenPlanes.Cartan.TraceJordanData
