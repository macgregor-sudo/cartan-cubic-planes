module

public import ThirteenPlanes.ChargeFixedReconnect

@[expose] public section

set_option backward.privateInPublic true

/-! Isometric extension of the one-loop contractions from an orthogonal factor. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes
namespace ChargeFixed

noncomputable section

open SymmetricCubic

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Extend a cubic by zero on the orthogonal complement of an isometric factor. -/
def extendCubic (f : U →ₗᵢ[ℝ] V) (h : SymmetricCubic U) : SymmetricCubic V :=
  h.pullback f.toLinearMap.adjoint

/-- Extend an endomorphism by zero on the orthogonal complement of a factor. -/
def extendEndomorphism (f : U →ₗᵢ[ℝ] V) (A : U →ₗ[ℝ] U) : V →ₗ[ℝ] V :=
  f.toLinearMap.comp (A.comp f.toLinearMap.adjoint)

@[simp] theorem extendEndomorphism_apply (f : U →ₗᵢ[ℝ] V) (A : U →ₗ[ℝ] U) (v : V) :
    extendEndomorphism f A v = f (A (f.toLinearMap.adjoint v)) := rfl

@[simp] theorem isometry_adjoint_apply (f : U →ₗᵢ[ℝ] V) (u : U) :
    f.toLinearMap.adjoint (f u) = u := by
  apply ext_inner_right ℝ
  intro x
  rw [LinearMap.adjoint_inner_left]
  exact f.inner_map_map u x

@[simp] theorem extendCubic_apply (f : U →ₗᵢ[ℝ] V) (h : SymmetricCubic U) (x y z : V) :
    (extendCubic f h).apply x y z =
      h.apply (f.toLinearMap.adjoint x) (f.toLinearMap.adjoint y) (f.toLinearMap.adjoint z) := by
  simp [extendCubic]

@[simp] theorem extendCubic_L (f : U →ₗᵢ[ℝ] V) (h : SymmetricCubic U) (v : V) :
    (extendCubic f h).L v = extendEndomorphism f (h.L (f.toLinearMap.adjoint v)) := by
  ext w
  apply ext_inner_right ℝ
  intro z
  change (extendCubic f h).apply v w z =
    ⟪f (h.L (f.toLinearMap.adjoint v) (f.toLinearMap.adjoint w)),z⟫
  rw [extendCubic_apply]
  exact LinearMap.adjoint_inner_right _ _ _

@[simp] theorem extendEndomorphism_mul (f : U →ₗᵢ[ℝ] V) (A B : U →ₗ[ℝ] U) :
    extendEndomorphism f A * extendEndomorphism f B = extendEndomorphism f (A*B) := by
  ext v
  simp only [mul_apply_eq_comp, extendEndomorphism_apply, isometry_adjoint_apply]

@[simp] theorem extendEndomorphism_trace (f : U →ₗᵢ[ℝ] V) (A : U →ₗ[ℝ] U) :
    LinearMap.trace ℝ V (extendEndomorphism f A) = LinearMap.trace ℝ U A := by
  unfold extendEndomorphism
  rw [LinearMap.trace_comp_comm' (A.comp f.toLinearMap.adjoint) f.toLinearMap]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, isometry_adjoint_apply]

@[simp] theorem extendCubic_doublePair (f : U →ₗᵢ[ℝ] V) (h g : SymmetricCubic U) (x y : V) :
    (extendCubic f h).doublePair (extendCubic f g) x y =
      h.doublePair g (f.toLinearMap.adjoint x) (f.toLinearMap.adjoint y) := by
  change LinearMap.trace ℝ V ((extendCubic f h).L x * (extendCubic f g).L y) = _
  simp only [extendCubic_L,extendEndomorphism_mul,extendEndomorphism_trace]
  rfl

@[simp] theorem extendCubic_doubleContraction (f : U →ₗᵢ[ℝ] V) (h : SymmetricCubic U) :
    (extendCubic f h).doubleContraction = extendEndomorphism f h.doubleContraction := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [extendEndomorphism_apply]
  change ⟪(extendCubic f h).doubleContraction x, y⟫ =
    ⟪f.toLinearMap (h.doubleContraction (f.toLinearMap.adjoint x)), y⟫
  rw [← f.toLinearMap.adjoint_inner_right]
  calc
    _ = (extendCubic f h).doublePair (extendCubic f h) x y := inner_doubleContraction _ _ _
    _ = _ := (extendCubic_doublePair f h h x y).trans (inner_doubleContraction _ _ _).symm

@[simp] theorem extendCubic_triangleContraction (f : U →ₗᵢ[ℝ] V) (h : SymmetricCubic U) :
    (extendCubic f h).triangleContraction = extendCubic f h.triangleContraction := by
  apply SymmetricCubic.ext
  intro x y z
  simp only [apply_triangleContraction,extendCubic_apply,extendCubic_L,
    extendEndomorphism_mul,extendEndomorphism_trace]

@[simp] theorem extendCubic_insert (f : U →ₗᵢ[ℝ] V) (h : SymmetricCubic U) (A : U →ₗ[ℝ] U) :
    (extendCubic f h).insert (extendEndomorphism f A) = extendCubic f (h.insert A) := by
  apply SymmetricCubic.ext
  intro x y z
  simp only [apply_insert,extendCubic_apply,extendEndomorphism_apply,isometry_adjoint_apply]

@[simp] theorem extendCubic_zero (f : U →ₗᵢ[ℝ] V) : extendCubic f 0 = 0 := by
  apply SymmetricCubic.ext
  intro x y z
  simp

private theorem apply_sub_cubic {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (a b : SymmetricCubic Y) (x y z : Y) :
    (a-b).apply x y z = a.apply x y z - b.apply x y z := by
  simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]

/-- One-loop beta commutes with isometric extension of a factor. -/
theorem extendCubic_oneLoopBeta (f : U →ₗᵢ[ℝ] V) (ε : ℝ) (h : SymmetricCubic U) :
    oneLoopBeta ε (extendCubic f h) = extendCubic f (oneLoopBeta ε h) := by
  apply SymmetricCubic.ext
  intro x y z
  simp only [oneLoopBeta,extendCubic_doubleContraction,extendCubic_triangleContraction,
    extendCubic_insert,apply_smul,apply_sub_cubic,extendCubic_apply]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
/-- Orthogonal factors annihilate one another under adjoint restriction. -/
theorem adjoint_orthogonal_apply (f : U →ₗᵢ[ℝ] V) (g : W →ₗᵢ[ℝ] V)
    (orthogonal : ∀ u w, ⟪f u,g w⟫ = 0) (w : W) : f.toLinearMap.adjoint (g w) = 0 := by
  apply ext_inner_right ℝ
  intro u
  rw [LinearMap.adjoint_inner_left, real_inner_comm, inner_zero_left]
  exact orthogonal u w

private theorem extendEndomorphism_mul_orthogonal (f : U →ₗᵢ[ℝ] V) (g : W →ₗᵢ[ℝ] V)
    (orthogonal : ∀ u w, ⟪f u,g w⟫ = 0) (A : U →ₗ[ℝ] U) (B : W →ₗ[ℝ] W) :
    extendEndomorphism f A * extendEndomorphism g B = 0 := by
  ext z
  simp only [mul_apply_eq_comp, extendEndomorphism_apply, adjoint_orthogonal_apply f g orthogonal,
    map_zero, LinearMap.zero_apply]

/-- There are no cross-sector contributions to the double contraction of two orthogonal factors. -/
theorem extendCubic_add_doubleContraction (f : U →ₗᵢ[ℝ] V) (g : W →ₗᵢ[ℝ] V)
    (orthogonal : ∀ u w, ⟪f u,g w⟫ = 0) (h : SymmetricCubic U) (k : SymmetricCubic W) :
    (extendCubic f h+extendCubic g k).doubleContraction =
      extendEndomorphism f h.doubleContraction + extendEndomorphism g k.doubleContraction := by
  have orthogonal' : ∀ w u, ⟪g w,f u⟫ = 0 := fun w u => (real_inner_comm _ _).trans (orthogonal u w)
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [← extendCubic_doubleContraction, ← extendCubic_doubleContraction]
  simp only [LinearMap.add_apply, inner_add_left, inner_doubleContraction, map_add, extendCubic_L,
    add_mul, mul_add, extendEndomorphism_mul_orthogonal f g orthogonal,
    extendEndomorphism_mul_orthogonal g f orthogonal', zero_add, add_zero]

/-- There are no cross-sector contributions to the triangle of two orthogonal factors. -/
theorem extendCubic_add_triangleContraction (f : U →ₗᵢ[ℝ] V) (g : W →ₗᵢ[ℝ] V)
    (orthogonal : ∀ u w, ⟪f u,g w⟫ = 0) (h : SymmetricCubic U) (k : SymmetricCubic W) :
    (extendCubic f h+extendCubic g k).triangleContraction =
      extendCubic f h.triangleContraction + extendCubic g k.triangleContraction := by
  have orthogonal' : ∀ w u, ⟪g w,f u⟫ = 0 := fun w u => (real_inner_comm _ _).trans (orthogonal u w)
  apply SymmetricCubic.ext
  intro x y z
  rw [← extendCubic_triangleContraction, ← extendCubic_triangleContraction]
  simp only [apply_triangleContraction,apply_add,map_add,LinearMap.add_apply,extendCubic_L]
  rw [add_mul, mul_add, mul_add]
  simp only [extendEndomorphism_mul_orthogonal f g orthogonal,
    extendEndomorphism_mul_orthogonal g f orthogonal', add_zero, zero_add, add_mul, mul_add]
  simp only [mul_assoc, extendEndomorphism_mul_orthogonal f g orthogonal,
    extendEndomorphism_mul_orthogonal g f orthogonal', mul_zero, add_zero, zero_add, map_add]

private theorem extendCubic_add_insert (f : U →ₗᵢ[ℝ] V) (g : W →ₗᵢ[ℝ] V)
    (orthogonal : ∀ u w, ⟪f u,g w⟫ = 0) (h : SymmetricCubic U) (k : SymmetricCubic W)
    (A : U →ₗ[ℝ] U) (B : W →ₗ[ℝ] W) :
    (extendCubic f h+extendCubic g k).insert (extendEndomorphism f A + extendEndomorphism g B) =
      extendCubic f (h.insert A) + extendCubic g (k.insert B) := by
  have orthogonal' : ∀ w u, ⟪g w,f u⟫ = 0 := fun w u => (real_inner_comm _ _).trans (orthogonal u w)
  apply SymmetricCubic.ext
  intro x y z
  simp only [apply_insert,apply_add,LinearMap.add_apply,extendCubic_apply,extendEndomorphism_apply,
    map_add,isometry_adjoint_apply,adjoint_orthogonal_apply f g orthogonal,
    adjoint_orthogonal_apply g f orthogonal',add_zero,zero_add]
  ring

/-- The actual tensor beta splits across two orthogonal, decoupled factors. -/
theorem extendCubic_add_oneLoopBeta (f : U →ₗᵢ[ℝ] V) (g : W →ₗᵢ[ℝ] V)
    (orthogonal : ∀ u w, ⟪f u,g w⟫ = 0) (ε : ℝ) (h : SymmetricCubic U) (k : SymmetricCubic W) :
    oneLoopBeta ε (extendCubic f h+extendCubic g k) =
      extendCubic f (oneLoopBeta ε h)+extendCubic g (oneLoopBeta ε k) := by
  rw [← extendCubic_oneLoopBeta, ← extendCubic_oneLoopBeta]
  unfold oneLoopBeta
  simp only [extendCubic_add_doubleContraction f g orthogonal,
    extendCubic_add_triangleContraction f g orthogonal, extendCubic_add_insert f g orthogonal,
    extendCubic_doubleContraction, extendCubic_triangleContraction]
  rw [← extendCubic_insert, ← extendCubic_insert]
  module


end
end ChargeFixed
end ThirteenPlanes
