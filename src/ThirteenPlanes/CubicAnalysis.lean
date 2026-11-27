module

public import ThirteenPlanes.CubicMetric
public import ThirteenPlanes.ChargeFixedExtension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.privateInPublic true

/-! Smoothness and differential of the one-loop field on the full real cubic space. -/

open scoped ContDiff RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace SymmetricCubic

/-- Evaluation at three fixed vectors is a continuous linear functional of the cubic. -/
def evaluate (x y z : V) : SymmetricCubic V →L[ℝ] ℝ :=
  (show SymmetricCubic V →ₗ[ℝ] ℝ from
    { toFun h := h.apply x y z
      map_add' h g := h.apply_add g x y z
      map_smul' r h := apply_smul r h x y z }).toContinuousLinearMap

@[simp] theorem evaluate_apply (x y z : V) (h : SymmetricCubic V) : evaluate x y z h = h.apply x y z := rfl

private def realEntryMap : SymmetricCubic V →ₗ[ℝ]
    (Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → ℝ) where
  toFun h := h.coefficient (stdOrthonormalBasis ℝ V)
  map_add' h g := by ext i j k; exact h.apply_add g _ _ _
  map_smul' r h := by ext i j k; exact apply_smul r h _ _ _

private theorem realEntryMap_injective : Function.Injective (realEntryMap (V := V)) := by
  intro h g hh
  have hz : realEntryMap (h-g) = 0 := by rw [map_sub,hh,sub_self]
  apply sub_eq_zero.mp
  apply eq_zero_of_tensorPairing_self
  rw [tensorPairing_eq_sum (stdOrthonormalBasis ℝ V)]
  change (∑ i, ∑ j, ∑ k, realEntryMap (h-g) i j k * realEntryMap (h-g) i j k) = 0
  simp [hz]

/-- Smoothness of a cubic-valued function follows from smoothness of its real evaluations. -/
theorem contDiff_of_evaluate {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ∞ω}
    {f : W → SymmetricCubic V} (h : ∀ x y z, ContDiff ℝ n (fun u => (f u).apply x y z)) :
    ContDiff ℝ n f := by
  obtain ⟨recover,hrecover⟩ := (realEntryMap (V := V)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (realEntryMap_injective (V := V)))
  have hb : f = recover.toContinuousLinearMap ∘ realEntryMap ∘ f := by
    funext u
    exact (congrArg (fun F : SymmetricCubic V →ₗ[ℝ] SymmetricCubic V => F (f u)) hrecover).symm
  rw [hb]
  apply recover.toContinuousLinearMap.contDiff.comp
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  rw [contDiff_pi]
  intro k
  exact h _ _ _

private theorem insertion_first_sum (h : SymmetricCubic V) (x y z : V) :
    h.apply (h.doubleContraction x) y z =
      ∑ a, (∑ b, ∑ c,
        h.apply x (stdOrthonormalBasis ℝ V b) (stdOrthonormalBasis ℝ V c) *
        h.apply (stdOrthonormalBasis ℝ V a) (stdOrthonormalBasis ℝ V b)
          (stdOrthonormalBasis ℝ V c)) * h.apply (stdOrthonormalBasis ℝ V a) y z := by
  let e := stdOrthonormalBasis ℝ V
  conv_lhs => rw [← e.sum_repr' (h.doubleContraction x), apply_sum₁ e]
  apply Finset.sum_congr rfl
  intro a _
  rw [real_inner_comm (h.doubleContraction x) (e a),inner_doubleContraction_eq_sum e]

omit [FiniteDimensional ℝ V] in
private theorem apply_sub_cubic (C D : SymmetricCubic V) (x y z : V) :
    (C-D).apply x y z = C.apply x y z - D.apply x y z := by
  simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]

end SymmetricCubic

open SymmetricCubic

/-- The physical one-loop field is smooth on the full space of real symmetric cubics. -/
theorem oneLoopBeta_contDiff (n : ℕ∞ω) (ε : ℝ) :
    ContDiff ℝ n (oneLoopBeta (V := V) ε) := by
  apply contDiff_of_evaluate
  intro x y z
  have he (x y z : V) : ContDiff ℝ n (fun h : SymmetricCubic V => h.apply x y z) := (evaluate x y z).contDiff
  have hi (x y z : V) : ContDiff ℝ n (fun h : SymmetricCubic V => h.apply (h.doubleContraction x) y z) := by
    simp_rw [insertion_first_sum]
    fun_prop
  have h₂ : ContDiff ℝ n (fun h : SymmetricCubic V => h.apply x (h.doubleContraction y) z) := by
    convert hi y x z using 1
    funext h
    exact h.apply_swap₁₂ x (h.doubleContraction y) z
  have h₃ : ContDiff ℝ n (fun h : SymmetricCubic V => h.apply x y (h.doubleContraction z)) := by
    convert hi z x y using 1
    funext h
    rw [h.apply_swap₂₃ x y, h.apply_swap₁₂ x (h.doubleContraction z)]
  have ht : ContDiff ℝ n (fun h : SymmetricCubic V => h.triangleContraction.apply x y z) := by
    simp_rw [apply_triangleContraction_eq_sum (stdOrthonormalBasis ℝ V)]
    fun_prop
  simp only [oneLoopBeta, apply_smul, apply_sub_cubic, apply_insert]
  fun_prop

/-- For the physical-time normalization, the derivative of beta is minus the A-Hessian
as a bilinear form, with the factor from the loop normalization. -/
theorem inner_fderiv_normalizedOneLoopBeta (C D k : SymmetricCubic V) :
    ⟪k, fderiv ℝ (oneLoopBeta (16 * Real.pi ^ 2)⁻¹) C D⟫ =
      -(16 * Real.pi^2)⁻¹ * aHessian C D k := by
  let ε := (16 * Real.pi^2)⁻¹
  let B := oneLoopBeta (V := V) ε
  have hd := ((oneLoopBeta_contDiff (V := V) 1 ε).differentiable (by simp) C).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => C+s • D) D 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const D |>.const_add C
  have hb : HasDerivAt (fun s : ℝ => B (C+s • D)) (fderiv ℝ B C D) 0 := by
    have hd' : HasFDerivAt B (fderiv ℝ B C) ((fun s : ℝ => C+s • D) 0) := by
      simpa only [zero_smul,add_zero] using hd
    exact HasFDerivAt.comp_hasDerivAt (l := B) (f := fun s : ℝ => C+s • D) 0 hd' hpath
  have h1 := (innerSL ℝ k).hasFDerivAt.comp_hasDerivAt 0 hb
  have h2 := (hasDerivAt_gradPair_aHessian C D k).const_mul (-ε)
  have hf : (fun s : ℝ => -ε * gradPair (C+s • D) k) =
      fun s : ℝ => ⟪k, B (C+s • D)⟫ := by
    funext s
    rw [gradPair,inner_eq_tensorPairing]
    change -ε * (-(16 * Real.pi^2) * k.tensorPairing (B (C+s • D))) = _
    have he : -ε * -(16 * Real.pi^2) = 1 := by
      dsimp [ε]
      rw [neg_mul_neg,inv_mul_cancel₀ (by positivity)]
    rw [← mul_assoc,he,one_mul]
  rw [hf] at h2
  exact h1.unique h2

end
end ThirteenPlanes
