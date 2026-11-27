module

public import ThirteenPlanes.CubicAnalysis
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! Exponentiating a skew linear endomorphism gives the finite rotation of a cubic. -/

open scoped ContDiff RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

local instance : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
local instance : NormedAlgebra ℚ (V →L[ℝ] V) := NormedAlgebra.restrictScalars ℚ ℝ _

open ChargeFixed

/-- The orthogonal transformation whose infinitesimal generator is the skew endomorphism. -/
def skewRotation (A : V →ₗ[ℝ] V) (hA : IsSkew A) : V ≃ₗᵢ[ℝ] V :=
  Unitary.linearIsometryEquiv ⟨NormedSpace.exp A.toContinuousLinearMap,
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff,ContinuousLinearMap.star_eq_adjoint]
      apply ContinuousLinearMap.ext
      intro y
      apply ext_inner_right ℝ
      intro x
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp only [neg_apply,inner_neg_left,LinearMap.coe_toContinuousLinearMap']
      calc
        _ = ⟪A x,y⟫ := real_inner_comm (A x) y
        _ = -⟪x,A y⟫ := hA x y
        _ = _ := congrArg Neg.neg (real_inner_comm (A y) x))⟩

@[simp] theorem skewRotation_apply (A : V →ₗ[ℝ] V) (hA : IsSkew A) (x : V) :
    skewRotation A hA x = NormedSpace.exp A.toContinuousLinearMap x := rfl

namespace SymmetricCubic

def clmTrilinear (C : SymmetricCubic V) : V →L[ℝ] (V →L[ℝ] (V →L[ℝ] ℝ)) :=
  let l₁ : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap.toLinearMap
  let l₂ : (V →ₗ[ℝ] (V →ₗ[ℝ] ℝ)) →ₗ[ℝ] (V →L[ℝ] (V →L[ℝ] ℝ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (l₁.compRight ℝ)
  let f : V →ₗ[ℝ] (V →L[ℝ] (V →L[ℝ] ℝ)) := l₂.comp C.trilinear
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (F' := (V →L[ℝ] (V →L[ℝ] ℝ))) f

@[simp] theorem clmTrilinear_apply (C : SymmetricCubic V) (x y z : V) :
    clmTrilinear C x y z = C.apply x y z := rfl

/-- Pull a cubic back by the exponential of an operator, without restricting the operator domain. -/
def exponentialPullback (C : SymmetricCubic V) (A : V →L[ℝ] V) : SymmetricCubic V :=
  C.pullback (NormedSpace.exp A).toLinearMap

@[simp] theorem exponentialPullback_zero (C : SymmetricCubic V) : C.exponentialPullback 0 = C := by
  apply SymmetricCubic.ext
  intro x y z
  simp [exponentialPullback]

/-- Pullback by the operator exponential is smooth. -/
theorem exponentialPullback_contDiff (C : SymmetricCubic V) (n : ℕ∞ω) :
    ContDiff ℝ n C.exponentialPullback := by
  apply contDiff_of_evaluate
  intro x y z
  have he : ContDiff ℝ n (NormedSpace.exp : (V →L[ℝ] V) → V →L[ℝ] V) :=
    AnalyticOnNhd.contDiff (fun a _ => NormedSpace.exp_analytic a)
  have hv (v : V) : ContDiff ℝ n (fun A : V →L[ℝ] V => NormedSpace.exp A v) :=
    he.clm_apply contDiff_const
  change ContDiff ℝ n (fun A : V →L[ℝ] V => (C.pullback (NormedSpace.exp A).toLinearMap).apply x y z)
  simp only [pullback_apply,ContinuousLinearMap.coe_coe]
  simp_rw [← clmTrilinear_apply C]
  exact (((clmTrilinear C).contDiff.comp (hv x)).clm_apply (hv y)).clm_apply (hv z)

/-- The derivative at the identity is the infinitesimal insertion action in all three slots. -/
theorem exponentialPullback_hasFDerivAt (C : SymmetricCubic V) :
    HasFDerivAt C.exponentialPullback
      (((insertLin C).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap) 0 := by
  let F := C.exponentialPullback
  let L : (V →L[ℝ] V) →L[ℝ] SymmetricCubic V :=
    ((insertLin C).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap
  change HasFDerivAt F L 0
  have hF := ((C.exponentialPullback_contDiff 1).differentiable (by simp) 0).hasFDerivAt
  have he : HasFDerivAt (NormedSpace.exp : (V →L[ℝ] V) → V →L[ℝ] V)
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) (0 : V →L[ℝ] V) := hasFDerivAt_exp_zero
  have hv (v : V) := he.clm_apply (hasFDerivAt_const v (0 : V →L[ℝ] V))
  have hd : fderiv ℝ F 0 = L := by
    apply ContinuousLinearMap.ext
    intro A
    apply SymmetricCubic.ext
    intro x y z
    have h1 := (evaluate x y z).hasFDerivAt.comp (0 : V →L[ℝ] V) hF
    have h2 := ((((clmTrilinear C).hasFDerivAt.comp (0 : V →L[ℝ] V) (hv x)).clm_apply (hv y)).clm_apply (hv z))
    have hfun : (fun A : V →L[ℝ] V => clmTrilinear C (NormedSpace.exp A x)
        (NormedSpace.exp A y) (NormedSpace.exp A z)) = evaluate x y z ∘ F := by
      funext B
      simp [F,exponentialPullback]
    rw [← hfun] at h1
    have heq := h1.unique h2
    have hA := congrArg (fun m : (V →L[ℝ] V) →L[ℝ] ℝ => m A) heq
    simpa [F,L,exponentialPullback,apply_insert, add_assoc,add_comm,add_left_comm] using hA
  exact hd ▸ hF

end SymmetricCubic

/-- Orthogonal pullback commutes with the actual one-loop field. -/
theorem oneLoopBeta_pullback_isometry (U : V ≃ₗᵢ[ℝ] V) (ε : ℝ) (h : SymmetricCubic V) :
    oneLoopBeta ε (h.pullback U.toLinearMap) = (oneLoopBeta ε h).pullback U.toLinearMap := by
  have eq (D : SymmetricCubic V) : D.pullback U.toLinearMap = extendCubic U.symm.toLinearIsometry D := by
    have ha (x : V) : U.symm.toLinearIsometry.toLinearMap.adjoint x = U x := by
      obtain ⟨y,rfl⟩ := U.symm.surjective x
      change U.symm.toLinearIsometry.toLinearMap.adjoint (U.symm.toLinearIsometry y) = _
      rw [isometry_adjoint_apply]
      exact (U.apply_symm_apply y).symm
    apply SymmetricCubic.ext
    intro x y z
    simp only [SymmetricCubic.pullback_apply, extendCubic_apply, ha, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
  rw [eq h,extendCubic_oneLoopBeta,eq (oneLoopBeta ε h)]


/-- Orthogonal pullback is a continuous linear equivalence of the cubic space. -/
def orthogonalPullback (U : V ≃ₗᵢ[ℝ] V) : SymmetricCubic V ≃L[ℝ] SymmetricCubic V :=
  (show SymmetricCubic V ≃ₗ[ℝ] SymmetricCubic V from
    { toFun := fun C => C.pullback U.toLinearMap
      invFun := fun C => C.pullback U.symm.toLinearMap
      left_inv := fun C => SymmetricCubic.ext (fun x y z => by simp)
      right_inv := fun C => SymmetricCubic.ext (fun x y z => by simp)
      map_add' := fun C D => SymmetricCubic.ext (fun x y z => by simp)
      map_smul' := fun a C => SymmetricCubic.ext (fun x y z => by simp) }).toContinuousLinearEquiv

@[simp] theorem orthogonalPullback_apply (U : V ≃ₗᵢ[ℝ] V) (C : SymmetricCubic V) :
    orthogonalPullback U C = C.pullback U.toLinearMap := rfl

end
end ThirteenPlanes
