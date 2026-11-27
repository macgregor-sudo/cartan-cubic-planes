module

public import ThirteenPlanes.Cartan.SecondRowLieMetricComparison
public import ThirteenPlanes.Cartan.SecondRowComplexFactors

@[expose] public section

/-! The metric comparison on the three concrete rows of the compact magic square. -/

namespace ThirteenPlanes.Cartan

noncomputable section

/-- The proportionality consumed by the Lie decomposition correspondence. -/
def SecondRowMetricAgreement {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    {M : TraceJordanData J} {K : Submodule ℝ (SkewOperator J)}
    (H : SecondRowCompactRealization M K) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ X Y : H.operators,
    (complexTraceForm X.val Y.val).re = a * (-killingForm ℝ H.operators X Y)

theorem complexSecondRow_metricAgreement (Q : SecondRowMagicSquareInput) :
    SecondRowMetricAgreement Q.complexRealization := by
  let H := Q.complexRealization
  let : LieAlgebra.IsSimple ℝ (secondRowCompactSU 3) := Q.complex_factor_simple
  exact secondRow_beta_eq_mul_negKilling_exchangedProduct complexJordan complexOperatorAlgebra
    H.operators H.carrier_eq H.compact (complexSecondRowFactorEquiv H.operators H.carrier_eq)
    (LinearEquiv.refl ℝ (secondRowCompactSU 3))
    (complexSecondRowFactorEquiv_exchange H.operators H.carrier_eq)

theorem quaternionSecondRow_metricAgreement (Q : SecondRowMagicSquareInput) :
    SecondRowMetricAgreement Q.quaternionRealization := by
  let H := Q.quaternionRealization
  let : LieAlgebra.IsSimple ℝ H.operators := Q.quaternion_simple
  exact secondRow_beta_eq_mul_negKilling_of_simple quaternionJordan quaternionOperatorAlgebra
    H.operators H.carrier_eq H.compact

theorem albertSecondRow_metricAgreement (Q : SecondRowMagicSquareInput) :
    SecondRowMetricAgreement Q.albertRealization := by
  let H := Q.albertRealization
  let : LieAlgebra.IsSimple ℝ H.operators := Q.albert_simple
  exact secondRow_beta_eq_mul_negKilling_of_simple albertJordan albertJordan.skewDerivations
    H.operators H.carrier_eq H.compact

/-- The three comparisons follow from the single quoted compact Lie identification. -/
theorem secondRowNamedMetricAgreement (Q : SecondRowMagicSquareInput) :
    SecondRowMetricAgreement Q.complexRealization ∧
      SecondRowMetricAgreement Q.quaternionRealization ∧
      SecondRowMetricAgreement Q.albertRealization :=
  ⟨complexSecondRow_metricAgreement Q, quaternionSecondRow_metricAgreement Q,
    albertSecondRow_metricAgreement Q⟩

end

end ThirteenPlanes.Cartan
