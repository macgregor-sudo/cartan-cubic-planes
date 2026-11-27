module

public import ThirteenPlanes.Cartan.InvariantMetric
public import ThirteenPlanes.Cartan.SecondRow.Involution

@[expose] public section

set_option backward.privateInPublic true

/-! Compare the actual second-row operator metric with its negative Killing form. -/

namespace ThirteenPlanes.Cartan

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- The real form of the literal complex trace pairing on the Lie operators. -/
def secondRowOperatorBeta (D : LieSubalgebra ℝ (Module.End ℂ (Complexified J))) : LinearMap.BilinForm ℝ D :=
  ((LinearMap.mul ℝ (Module.End ℂ (Complexified J))).compl₁₂ D.toSubmodule.subtype D.toSubmodule.subtype).compr₂
    (Complex.reCLM.toLinearMap.comp ((-LinearMap.trace ℂ (Complexified J)).restrictScalars ℝ))

@[simp] theorem secondRowOperatorBeta_apply (D : LieSubalgebra ℝ (Module.End ℂ (Complexified J))) (X Y : D) :
    secondRowOperatorBeta (J := J) D X Y = (complexTraceForm X.val Y.val).re := rfl

variable (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))

variable (D : LieSubalgebra ℝ (Module.End ℂ (Complexified J)))
variable (hD : D.toSubmodule = secondRowSpace M K)

include hD

private def lieOperatorsToSpace : D ≃ₗ[ℝ] secondRowSpace M K :=
  LinearEquiv.ofEq D.toSubmodule (secondRowSpace M K) hD

/-- The second-row conjugation as a Lie automorphism of the same operators. -/
def secondRowLieTheta : D ≃ₗ⁅ℝ⁆ D := by
  let e := lieOperatorsToSpace M K D hD
  let θ := e.trans ((secondRowTheta M K).trans e.symm)
  refine { θ with map_lie' := ?_ }
  intro X Y
  apply Subtype.ext
  change (secondRowTheta M K (e ⁅X, Y⁆)).val =
    operatorBracket (secondRowTheta M K (e X)).val (secondRowTheta M K (e Y)).val
  exact secondRowTheta_preserves_operatorBracket M K (e X) (e Y) (e ⁅X, Y⁆) rfl

theorem secondRowLieTheta_onSpace (X : secondRowSpace M K) :
    secondRowLieTheta M K D hD ((LinearEquiv.ofEq (secondRowSpace M K) D.toSubmodule hD.symm) X) =
      (LinearEquiv.ofEq (secondRowSpace M K) D.toSubmodule hD.symm) (secondRowTheta M K X) := by
  change (lieOperatorsToSpace M K D hD).symm
      (secondRowTheta M K ((lieOperatorsToSpace M K D hD)
        ((lieOperatorsToSpace M K D hD).symm X))) =
    (lieOperatorsToSpace M K D hD).symm (secondRowTheta M K X)
  rw [LinearEquiv.apply_symm_apply]

variable [FiniteDimensional ℝ J]

theorem secondRowOperatorBeta_isInvariantPositive :
    IsInvariantPositiveForm (secondRowOperatorBeta (J := J) D) where
  symmetric := fun X Y => by
    simp only [secondRowOperatorBeta_apply, complexTraceForm]
    rw [LinearMap.trace_mul_comm]
  positive := fun X hX => by
    let e := lieOperatorsToSpace M K D hD
    have he : e X ≠ 0 := fun he => hX (e.injective (he.trans (map_zero e).symm))
    exact (secondRow_traceForm_pos M K he).2
  invariant := fun X Y Z => by
    simp only [secondRowOperatorBeta_apply, complexTraceForm]
    change (-LinearMap.trace ℂ (Complexified J) (⁅X.val, Y.val⁆ * Z.val)).re =
      (-LinearMap.trace ℂ (Complexified J) (X.val * ⁅Y.val, Z.val⁆)).re
    rw [LinearMap.trace_lie_mul_eq]

theorem secondRowLieTheta_preserves_beta (X Y : D) :
    secondRowOperatorBeta (J := J) D (secondRowLieTheta M K D hD X) (secondRowLieTheta M K D hD Y) =
      secondRowOperatorBeta (J := J) D X Y := by
  let e := lieOperatorsToSpace M K D hD
  change (complexTraceForm (secondRowTheta M K (e X)).val (secondRowTheta M K (e Y)).val).re =
    (complexTraceForm (e X).val (e Y).val).re
  rw [secondRowTheta_preserves_traceForm]

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G]
  [FiniteDimensional ℝ G] [LieAlgebra.IsSimple ℝ G]

/-- A compact simple second-row identification makes the two metrics proportional. -/
theorem secondRow_beta_eq_mul_negKilling_simple (compact : CompactKilling D) (e : D ≃ₗ⁅ℝ⁆ G) :
    ∃ a : ℝ, 0 < a ∧ ∀ X Y : D,
      (complexTraceForm X.val Y.val).re = a * (-killingForm ℝ D X Y) := by
  have hA := (negativeKilling_isInvariantPositive (G := ↥D) compact).pullback e.symm
  have hB := (secondRowOperatorBeta_isInvariantPositive M K D hD).pullback e.symm
  obtain ⟨a, ha, heq⟩ := invariantPositiveForms_eq_mul hA hB
  refine ⟨a, ha, fun X Y => ?_⟩
  have h := heq (e X) (e Y)
  change (complexTraceForm (e.symm (e X)).val (e.symm (e Y)).val).re =
    a * (-killingForm ℝ D (e.symm (e X)) (e.symm (e Y))) at h
  simpa only [LieEquiv.symm_apply_apply] using h

/-- In the simple rows the native operator algebra itself can supply the simple type. -/
theorem secondRow_beta_eq_mul_negKilling_of_simple
    [LieAlgebra.IsSimple ℝ ↥D] (compact : CompactKilling D) :
    ∃ a : ℝ, 0 < a ∧ ∀ X Y : D,
      (complexTraceForm X.val Y.val).re = a * (-killingForm ℝ D X Y) := by
  let e : secondRowSpace M K ≃ₗ[ℝ] D := (lieOperatorsToSpace M K D hD).symm
  let f : secondRowSpace M K →ₗ[ℝ] D := e.toLinearMap
  have hf : Function.Surjective f := e.surjective
  let : Module.Finite ℝ ↥D := Module.Finite.of_surjective f hf
  exact secondRow_beta_eq_mul_negKilling_simple M K D hD compact (LieEquiv.refl : ↥D ≃ₗ⁅ℝ⁆ ↥D)

/-- If the product identification exchanges the factors under conjugation, the same positive
scalar compares the metrics on the whole second row. -/
theorem secondRow_beta_eq_mul_negKilling_exchangedProduct
    {H : Type*} [LieRing H] [LieAlgebra ℝ H] (compact : CompactKilling D)
    (e : D ≃ₗ⁅ℝ⁆ G × H) (s : G ≃ₗ[ℝ] H)
    (hexchange : ∀ x : G, e (secondRowLieTheta M K D hD (e.symm (x, 0))) = (0, s x)) :
    ∃ a : ℝ, 0 < a ∧ ∀ X Y : D,
      (complexTraceForm X.val Y.val).re = a * (-killingForm ℝ D X Y) := by
  let θ := secondRowLieTheta M K D hD
  let θ₀ (x : G × H) := e (θ (e.symm x))
  let f := e.symm.toLinearEquiv.toLinearMap
  let A := (-killingForm ℝ D).compl₁₂ f f
  let B := (secondRowOperatorBeta (J := J) D).compl₁₂ f f
  have hA : IsInvariantPositiveForm A := (negativeKilling_isInvariantPositive (G := ↥D) compact).pullback e.symm
  have hB : IsInvariantPositiveForm B := (secondRowOperatorBeta_isInvariantPositive M K D hD).pullback e.symm
  have hθA (x y : G × H) : A (θ₀ x) (θ₀ y) = A x y := by
    change -killingForm ℝ D (e.symm (e (θ (e.symm x)))) (e.symm (e (θ (e.symm y)))) =
      -killingForm ℝ D (e.symm x) (e.symm y)
    rw [LieEquiv.symm_apply_apply, LieEquiv.symm_apply_apply, LieAlgebra.killingForm_of_equiv_apply]
  have hθB (x y : G × H) : B (θ₀ x) (θ₀ y) = B x y := by
    change secondRowOperatorBeta (J := J) D (e.symm (e (θ (e.symm x)))) (e.symm (e (θ (e.symm y)))) =
      secondRowOperatorBeta (J := J) D (e.symm x) (e.symm y)
    rw [LieEquiv.symm_apply_apply, LieEquiv.symm_apply_apply]
    exact secondRowLieTheta_preserves_beta M K D hD _ _
  obtain ⟨a, ha, heq⟩ :=
    invariantPositiveForms_exchangedProduct_eq_mul hA hB s θ₀ hexchange hθA hθB
  refine ⟨a, ha, fun X Y => ?_⟩
  have h := heq (e X) (e Y)
  change (complexTraceForm (e.symm (e X)).val (e.symm (e Y)).val).re =
    a * (-killingForm ℝ D (e.symm (e X)) (e.symm (e Y))) at h
  simpa only [LieEquiv.symm_apply_apply] using h

end

end ThirteenPlanes.Cartan
