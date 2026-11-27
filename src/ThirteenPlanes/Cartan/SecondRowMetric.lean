module

public import ThirteenPlanes.Cartan.SecondRow

@[expose] public section

set_option backward.privateInPublic true

/-! Positivity of minus the complex operator trace on the real second row. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace TensorProduct

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

private theorem trace_skew_leftMul_zero (M : TraceJordanData J) (D : SkewOperator J) (x : J) :
    LinearMap.trace ℝ J (D.val * M.L x) = 0 := by
  let b := stdOrthonormalBasis ℝ J
  have hs : LinearMap.trace ℝ J (D.val * M.L x) =
      -∑ i, ⟪D.val (b i), M.L x (b i)⟫ := by
    rw [SymmetricCubic.trace_eq_sum_inner b, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change ⟪b i, D.val (M.L x (b i))⟫ = -⟪D.val (b i), M.L x (b i)⟫
    rw [D.property, neg_neg]
  have hm : LinearMap.trace ℝ J (M.L x * D.val) =
      ∑ i, ⟪D.val (b i), M.L x (b i)⟫ := by
    rw [SymmetricCubic.trace_eq_sum_inner b]
    apply Finset.sum_congr rfl
    intro i _
    change ⟪b i, M.L x (D.val (b i))⟫ = _
    rw [← M.assoc_inner]
    exact real_inner_comm _ _
  rw [LinearMap.trace_mul_comm] at hs
  rw [hm] at hs
  rw [LinearMap.trace_mul_comm, hm]
  linarith

private theorem trace_leftMul_sq (M : TraceJordanData J) (x : J) :
    LinearMap.trace ℝ J (M.L x * M.L x) =
      ∑ i, ‖M.L x (stdOrthonormalBasis ℝ J i)‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ J
  rw [SymmetricCubic.trace_eq_sum_inner b]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪b i, M.L x (M.L x (b i))⟫ = ‖M.L x (b i)‖ ^ 2
  rw [← M.assoc_inner, real_inner_self_eq_norm_sq]

private theorem trace_leftMul_sq_pos (M : TraceJordanData J) {x : J} (hx : x ≠ 0) :
    0 < LinearMap.trace ℝ J (M.L x * M.L x) := by
  let b := stdOrthonormalBasis ℝ J
  rw [trace_leftMul_sq]
  have hn : 0 ≤ ∑ i, ‖M.L x (b i)‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_contra! h
  have hz := le_antisymm h hn
  have hl : M.L x = 0 := by
    apply b.toBasis.ext
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hz i
      (Finset.mem_univ i)
    change M.L x (b i) = 0
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  exact hx (M.L_injective (by simpa only [map_zero] using hl))

/-- The actual complex trace form is real and splits into its two indicated real trace terms. -/
theorem secondRow_traceForm (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))
    (p q : K × M.traceFree) :
    complexTraceForm (secondRowEmbed M K p) (secondRowEmbed M K q) =
      ((⟪p.1.val, q.1.val⟫ + LinearMap.trace ℝ J (M.L p.2.val * M.L q.2.val) : ℝ) : ℂ) := by
  change complexTraceForm (realImagOperator p.1.val.val (M.L p.2.val))
    (realImagOperator q.1.val.val (M.L q.2.val)) = _
  have hc : LinearMap.trace ℝ J (M.L p.2.val * q.1.val.val) = 0 := by
    rw [LinearMap.trace_mul_comm]
    exact trace_skew_leftMul_zero M q.1.val p.2.val
  rw [complexTraceForm_realImag, trace_skew_leftMul_zero M p.1.val, hc,
    zero_add, Complex.ofReal_zero, mul_zero, sub_zero, skewOperator_inner]

/-- The minus-trace form in Proposition 7 is positive definite on the full actual real operator
space (K+iL(V)). Its diagonal is real in the complex representation. -/
theorem secondRow_traceForm_pos (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))
    {X : secondRowSpace M K} (hX : X ≠ 0) :
    (complexTraceForm X.val X.val).im = 0 ∧ 0 < (complexTraceForm X.val X.val).re := by
  obtain ⟨p, rfl⟩ := (secondRowCoordinates M K).surjective X
  change (complexTraceForm (secondRowEmbed M K p) (secondRowEmbed M K p)).im = 0 ∧
    0 < (complexTraceForm (secondRowEmbed M K p) (secondRowEmbed M K p)).re
  rw [secondRow_traceForm]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  have hp : p ≠ 0 := by
    intro h
    exact hX (h ▸ (secondRowCoordinates M K).map_zero)
  by_cases hx : p.2.val = 0
  · have hδ : p.1.val ≠ 0 := by
      intro hd
      exact hp (Prod.ext (Subtype.ext hd) (Subtype.ext hx))
    rw [hx, map_zero, zero_mul, map_zero, add_zero]
    exact real_inner_self_pos.mpr hδ
  · exact add_pos_of_nonneg_of_pos real_inner_self_nonneg (trace_leftMul_sq_pos M hx)

end

end ThirteenPlanes.Cartan
