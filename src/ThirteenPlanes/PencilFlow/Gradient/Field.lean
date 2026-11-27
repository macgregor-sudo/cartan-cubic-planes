module

public import ThirteenPlanes.EikonalRigidityStatements

@[expose] public section

set_option backward.privateInPublic true

/-! Lemma 9-gradient (one-loop potential gradient): the rescaled one-loop field is minus the gradient of the
A-function for the coefficient metric on cubics, and the A-function decreases along every solution
at the rate `‖rescaledField‖²`.

The coefficient metric is the instance of `ThirteenPlanes.CubicMetric`, whose inner product is
`tensorPairing` by definition. The directional derivatives are `ThirteenPlanes.aFunction_hasDerivAt`;
smoothness comes from writing the A-function as a polynomial in coefficient evaluations. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology ContDiff

namespace ThirteenPlanes.PencilFlow.Proofs

noncomputable section

open ThirteenPlanes ThirteenPlanes.SymmetricCubic ThirteenPlanes.PencilFlow.Statements

section Bridges

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
private theorem apply_sub' (C D : SymmetricCubic V) (x y z : V) :
    (C - D).apply x y z = C.apply x y z - D.apply x y z := by
  simp [apply, SymmetricCubic.L, inner_sub_left]

private theorem doubleContraction_smul (a : ℝ) (κ : SymmetricCubic V) :
    (a • κ).doubleContraction = (a ^ 2) • κ.doubleContraction := by
  apply LinearMap.ext; intro x
  apply ext_inner_right ℝ; intro y
  simp only [inner_doubleContraction, LinearMap.smul_apply, real_inner_smul_left, map_smul,
    smul_mul_smul_comm, smul_eq_mul]
  ring

private theorem triangleContraction_smul (a : ℝ) (κ : SymmetricCubic V) :
    (a • κ).triangleContraction = (a ^ 3) • κ.triangleContraction := by
  apply SymmetricCubic.ext; intro x y z
  rw [apply_triangleContraction, apply_smul, apply_triangleContraction]
  simp only [map_smul, LinearMap.smul_apply, smul_mul_smul_comm, smul_eq_mul]
  ring

private theorem insert_smul_left (a : ℝ) (κ : SymmetricCubic V) (A : V →ₗ[ℝ] V) :
    (a • κ).insert A = a • κ.insert A := by
  apply SymmetricCubic.ext; intro x y z
  simp only [apply_insert, apply_smul]
  ring

/-- The rescaled field in terms of the normalized loop field. -/
theorem rescaledField_eq_oneLoopBeta (κ : SymmetricCubic V) :
    rescaledField κ = (16 * Real.pi ^ 2) • oneLoopBeta (16 * Real.pi ^ 2)⁻¹ κ := by
  have hπ : (16 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  apply SymmetricCubic.ext; intro x y z
  simp only [rescaledField, oneLoopBeta, apply_smul, apply_sub']
  field_simp
  ring

/-- The A-function is a polynomial in the coefficients, hence smooth. -/
theorem aFunction_contDiff (n : ℕ∞ω) : ContDiff ℝ n (aFunction (V := V)) := by
  let e := stdOrthonormalBasis ℝ V
  have he (x y z : V) : ContDiff ℝ n (fun h : SymmetricCubic V => h.apply x y z) :=
    (evaluate x y z).contDiff
  have hf : (aFunction (V := V)) = fun κ : SymmetricCubic V =>
      -(1 / 4) * (∑ i, ∑ j, ∑ k, κ.coefficient e i j k * κ.coefficient e i j k) +
        3 / 8 * Coords.quadSum (κ.coefficient e) (κ.coefficient e) (κ.coefficient e)
          (κ.coefficient e) +
        1 / 2 * Coords.tetSum (κ.coefficient e) (κ.coefficient e) (κ.coefficient e)
          (κ.coefficient e) := by
    funext κ
    rw [aFunction, tensorPairing_eq_sum e, doubleTraceSq_eq e, tetrahedron_eq e]
  rw [hf]
  simp only [Coords.quadSum, Coords.quadTerm, Coords.tetSum, Coords.tetTerm, coefficient]
  fun_prop

theorem aFunction_hasFDerivAt (κ : SymmetricCubic V) :
    HasFDerivAt aFunction
      (InnerProductSpace.toDual ℝ (SymmetricCubic V) (-rescaledField κ) :
        SymmetricCubic V →L[ℝ] ℝ) κ := by
  have hd : DifferentiableAt ℝ (aFunction (V := V)) κ :=
    (aFunction_contDiff 1).differentiable (by simp) κ
  have hfd := hd.hasFDerivAt
  convert hfd using 1
  refine ContinuousLinearMap.ext fun k => ?_
  have hpath : HasDerivAt (fun s : ℝ => κ + s • k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add κ
  have hfd' : HasFDerivAt aFunction (fderiv ℝ aFunction κ) ((fun s : ℝ => κ + s • k) 0) := by
    simpa only [zero_smul, add_zero] using hfd
  have h1 := hfd'.comp_hasDerivAt (0 : ℝ) hpath
  have h2 := aFunction_hasDerivAt κ k
  have huniq := h1.unique h2
  rw [InnerProductSpace.toDual_apply_apply, inner_eq_tensorPairing, Function.comp_def] at *
  rw [huniq, rescaledField_eq_oneLoopBeta, tensorPairing_comm, ← neg_one_smul ℝ,
    smul_smul, tensorPairing_smul_right]
  ring

end Bridges

/-- One-loop potential gradient, scaling: the physical field at `h = 4π√ε κ` is the rescaled field. -/
theorem gradientScaling (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.GradientScaling V := by
  intro ε hε κ
  have hπ : (16 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  rw [oneLoopBeta, doubleContraction_smul, triangleContraction_smul, insert_smul_left,
    insert_smul]
  apply SymmetricCubic.ext; intro x y z
  simp only [rescaledField, apply_smul, apply_sub']
  generalize Real.sqrt ε = s at hs ⊢
  subst hs
  field_simp
  ring

/-- One-loop potential gradient, the A-function and the two forms of its tetrahedral term. -/
theorem gradientPotential (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.GradientPotential V := by
  intro e κ
  exact ⟨rfl, rfl, tetrahedron_eq e κ⟩

/-- One-loop potential gradient, the gradient for the coefficient metric. -/
theorem gradientOfOneLoopPotential (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.Gradient V := by
  intro κ
  exact hasGradientAt_iff_hasFDerivAt.mpr (aFunction_hasFDerivAt κ)

/-- One-loop potential gradient, dissipation along any integral curve, one-sided endpoints included. -/
theorem gradientDissipation (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.GradientDissipation V := by
  intro trajectory times hcurve s hs
  have h := (aFunction_hasFDerivAt (trajectory s)).comp_hasDerivWithinAt s (hcurve s hs)
  convert h using 1
  rw [InnerProductSpace.toDual_apply_apply, inner_neg_left, real_inner_self_eq_norm_sq]

end

end ThirteenPlanes.PencilFlow.Proofs
