module

public import CompositionAlgebras.Composition.Classification
public import Mathlib.Analysis.Quaternion
public import Mathlib.Tactic.Linarith
public import OctonionGeometry

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.MarkedPlane

open scoped Quaternion RealInnerProductSpace

noncomputable section

local notation "𝕆ₙ" => AlbertSequential.Octonion

namespace NativeOctonionEuclidean

@[instance_reducible]
private def core : InnerProductSpace.Core ℝ 𝕆ₙ where
  inner := AlbertSequential.octDot
  conj_inner_symm x y := AlbertSequential.octDot_comm y x
  re_inner_nonneg := AlbertSequential.octNormSq_nonneg
  definite x := (AlbertSequential.octNormSq_eq_zero x).mp
  add_left := AlbertSequential.octDot_add_left
  smul_left x y r := AlbertSequential.octDot_smul_left r x y

/-- Euclidean norm from the real part of multiplication by the conjugate. -/
scoped instance normedAddCommGroup : NormedAddCommGroup 𝕆ₙ :=
  core.toNormedAddCommGroup

scoped instance innerProductSpace : InnerProductSpace ℝ 𝕆ₙ := by
  letI := core
  exact InnerProductSpace.ofCore inferInstance

end NativeOctonionEuclidean

open scoped NativeOctonionEuclidean

theorem nativeOctonion_inner (x y : 𝕆ₙ) : ⟪x, y⟫ = AlbertSequential.octDot x y := rfl

theorem nativeOctonion_norm_sq (x : 𝕆ₙ) : ‖x‖ ^ 2 = AlbertSequential.octNormSq x :=
  (real_inner_self_eq_norm_sq x).symm

private def cdToNative : CompositionAlgebra.CD (Quaternion ℝ) ≃ₗ[ℝ] 𝕆ₙ where
  toFun x := (x.fst, x.snd)
  invFun x := CompositionAlgebra.CD.mk x.1 x.2
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem cdToNative_mul (a b : CompositionAlgebra.CD (Quaternion ℝ)) :
    cdToNative (a * b) = AlbertSequential.octonionMul (cdToNative a) (cdToNative b) := by
  have hstar (q : Quaternion ℝ) : CompositionAlgebra.cstar q = star q := by
    apply Quaternion.ext <;> simp [Quaternion.cstar_eq]
  change (a.fst * b.fst - CompositionAlgebra.cstar b.snd * a.snd,
      b.snd * a.fst + a.snd * CompositionAlgebra.cstar b.fst) =
    (a.fst * b.fst - star b.snd * a.snd, b.snd * a.fst + a.snd * star b.fst)
  rw [hstar, hstar]

private theorem cdToNative_norm_sq (x : CompositionAlgebra.CD (Quaternion ℝ)) :
    ‖cdToNative x‖ ^ 2 = CompositionAlgebra.nf x := by
  rw [nativeOctonion_norm_sq, AlbertSequential.octNormSq_eq_coords,
    CompositionAlgebra.CD.nf_eq, Quaternion.nf_eq, Quaternion.nf_eq]
  change x.fst.re ^ 2 + x.fst.imI ^ 2 + x.fst.imJ ^ 2 + x.fst.imK ^ 2 +
    x.snd.re ^ 2 + x.snd.imI ^ 2 + x.snd.imJ ^ 2 + x.snd.imK ^ 2 = _
  ring

/-- The Fano-basis octonion of the Hurwitz theorem in native Cayley–Dickson coordinates. -/
def hurwitzOctonionToNative : _root_.Octonion ≃ₗ[ℝ] 𝕆ₙ :=
  CompositionAlgebra.cdQuaternionEquiv.symm.trans cdToNative

theorem hurwitzOctonionToNative_mul (x y : _root_.Octonion) :
    hurwitzOctonionToNative (x * y) =
      AlbertSequential.octonionMul (hurwitzOctonionToNative x) (hurwitzOctonionToNative y) := by
  change cdToNative (CompositionAlgebra.cdQuaternionEquiv.symm (x * y)) = _
  rw [CompositionAlgebra.cdQuaternionEquiv_isCompIso.symm.map_mul, cdToNative_mul]
  rfl

theorem hurwitzOctonionToNative_norm_sq (x : _root_.Octonion) :
    ‖hurwitzOctonionToNative x‖ ^ 2 = CompositionAlgebra.nf x := by
  change ‖cdToNative (CompositionAlgebra.cdQuaternionEquiv.symm x)‖ ^ 2 = _
  rw [cdToNative_norm_sq, CompositionAlgebra.cdQuaternionEquiv_isCompIso.symm.map_nf]

/-- The coefficient pairing in the native model is the Hurwitz composition form. -/
theorem hurwitzOctonionToNative_inner (x y : _root_.Octonion) :
    AlbertSequential.octDot (hurwitzOctonionToNative x) (hurwitzOctonionToNative y) =
      CompositionAlgebra.ip x y := by
  rw [← nativeOctonion_inner]
  have h := hurwitzOctonionToNative_norm_sq (x + y)
  rw [map_add, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    real_inner_comm (hurwitzOctonionToNative x) (hurwitzOctonionToNative y),
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    hurwitzOctonionToNative_norm_sq, hurwitzOctonionToNative_norm_sq,
    CompositionAlgebra.nf_add] at h
  linarith

end
end ThirteenPlanes.MarkedPlane
