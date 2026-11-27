module

public import ThirteenPlanes.HessianSpectrum.Basic

@[expose] public section

set_option backward.privateInPublic true

/-! The coefficient pairing as the Euclidean metric on real symmetric cubics. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.SymmetricCubic

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private instance tensorPairingCore : InnerProductSpace.Core ℝ (SymmetricCubic V) where
  inner := tensorPairing
  conj_inner_symm x y := by simpa only [RCLike.conj_to_real] using tensorPairing_comm y x
  re_inner_nonneg x := tensorPairing_self_nonneg x
  add_left x y z := tensorPairing_add_left z x y
  smul_left x y r := by
    rw [tensorPairing_comm (r • x),tensorPairing_smul_right,tensorPairing_comm y x]
    rfl
  definite x := (tensorPairing_self_eq_zero_iff x).mp

noncomputable instance : NormedAddCommGroup (SymmetricCubic V) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance : InnerProductSpace ℝ (SymmetricCubic V) :=
  InnerProductSpace.ofCore (𝕜 := ℝ) (F := SymmetricCubic V) inferInstance

@[simp] theorem inner_eq_tensorPairing (x y : SymmetricCubic V) : ⟪x,y⟫ = x.tensorPairing y := rfl

end
end ThirteenPlanes.SymmetricCubic
