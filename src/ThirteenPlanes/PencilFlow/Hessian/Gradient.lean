module

public import ThirteenPlanes.PencilFlow.Gradient.Field

@[expose] public section

/-! The rescaled gradient and its derivative in the coefficient metric of the Hessian. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology

namespace ThirteenPlanes.PencilFlow.HessianBridge

noncomputable section

open SymmetricCubic Statements

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The A-function is smooth (a polynomial in the coefficients). -/
theorem aFunction_contDiff : ContDiff ℝ 1 (aFunction (V := V)) :=
  Proofs.aFunction_contDiff 1

theorem sixteen_pi_sq_ne_zero : (16 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity

/-- The rescaled field is `16π²` times the physical field at `ε = 1/(16π²)`. -/
theorem rescaledField_eq (κ : SymmetricCubic V) :
    rescaledField κ = (16 * Real.pi ^ 2) • oneLoopBeta (16 * Real.pi ^ 2)⁻¹ κ :=
  Proofs.rescaledField_eq_oneLoopBeta κ

theorem rescaledField_fun_eq :
    (rescaledField (V := V)) = fun κ => (16 * Real.pi ^ 2) • oneLoopBeta (16 * Real.pi ^ 2)⁻¹ κ :=
  funext rescaledField_eq

theorem rescaledField_contDiff (n : ℕ∞) : ContDiff ℝ n (rescaledField (V := V)) := by
  rw [rescaledField_fun_eq]
  exact (contDiff_const (c := (16 * Real.pi ^ 2 : ℝ))).smul (oneLoopBeta_contDiff (V := V) n _)

/-- The Fréchet derivative of the A-function is the Riesz dual of `-rescaledField`. -/
theorem aFunction_hasFDerivAt (κ : SymmetricCubic V) :
    HasFDerivAt aFunction
      (InnerProductSpace.toDual ℝ (SymmetricCubic V) (-rescaledField κ)) κ :=
  Proofs.aFunction_hasFDerivAt κ

/-- The gradient of the A-function in the coefficient metric. -/
theorem aFunction_hasGradientAt (κ : SymmetricCubic V) :
    HasGradientAt aFunction (-rescaledField κ) κ :=
  Proofs.gradientOfOneLoopPotential V κ

theorem gradient_aFunction : gradient (aFunction (V := V)) = fun κ => -rescaledField κ :=
  funext fun κ => (aFunction_hasGradientAt κ).gradient

/-- The derivative of the rescaled field pairs as minus the old Hessian form. -/
theorem inner_fderiv_rescaledField (C D k : SymmetricCubic V) :
    ⟪k, fderiv ℝ rescaledField C D⟫ = -aHessian C D k := by
  have hdiff : DifferentiableAt ℝ (oneLoopBeta (V := V) (16 * Real.pi ^ 2)⁻¹) C :=
    (oneLoopBeta_contDiff 1 _).differentiable one_ne_zero C
  rw [rescaledField_fun_eq, fderiv_fun_const_smul hdiff, smul_apply,
    real_inner_smul_right, inner_fderiv_normalizedOneLoopBeta]
  field_simp [sixteen_pi_sq_ne_zero]

/-- **Hessian operator bridge.** `⟪k, H_C D⟫ = aHessian C D k` for the `hessianOperator`. -/
theorem inner_hessianOperator (C D k : SymmetricCubic V) :
    ⟪k, hessianOperator C D⟫ = aHessian C D k := by
  have hdiff : DifferentiableAt ℝ (rescaledField (V := V)) C :=
    (rescaledField_contDiff 1).differentiable one_ne_zero C
  unfold hessianOperator
  rw [gradient_aFunction, fderiv_fun_neg]
  change ⟪k, -(fderiv ℝ rescaledField C D)⟫ = _
  rw [inner_neg_right, inner_fderiv_rescaledField, neg_neg]

theorem hessianOperator_eq_iff (C D Y : SymmetricCubic V) :
    hessianOperator C D = Y ↔ ∀ k, aHessian C D k = Y.tensorPairing k := by
  constructor
  · rintro rfl k
    rw [← inner_hessianOperator, real_inner_comm, inner_eq_tensorPairing]
  · intro h
    apply ext_inner_left ℝ
    intro k
    rw [inner_hessianOperator, h, inner_eq_tensorPairing, tensorPairing_comm]

end

end ThirteenPlanes.PencilFlow.HessianBridge
