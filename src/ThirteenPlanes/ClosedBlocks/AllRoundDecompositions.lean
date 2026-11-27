module

public import ThirteenPlanes.ClosedBlocks.Classification
public import ThirteenPlanes.Reducible.FourLines
public import ThirteenPlanes.Nonharmonic.Classification

@[expose] public section

set_option backward.privateInPublic true

/-! Theorem A(ii) for all positive-strength eikonal cubics. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open Peirce RoundCubics

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

variable {h : SymmetricCubic V} {ι : Type*} [Fintype ι]

/-- The dimension-four nonharmonic alternative on its given decomposition. -/
def FourLinePattern (d : Decomposition h ι) : Prop :=
  Module.finrank ℝ V = 4 ∧ ¬ h.TraceFree ∧ Fintype.card ι = 4 ∧
    ∀ i, Module.finrank ℝ (d.piece i) = 1

/-- Four lines in dimension four, or one of the three harmonic patterns. -/
def RoundDecompositionPattern (c : ℝ) (d : Decomposition h ι) : Prop :=
  FourLinePattern d ∨ (h.TraceFree ∧ HarmonicBlockDecompositionPattern c d)

private theorem reducible_dimension_pattern {c : ℝ}
    (round : IsRound h c) (d : Decomposition h ι) (proper : 1 < Fintype.card ι)
    {a : V} (ha : ‖a‖ = 1)
    (diagonal : ∀ x : V, h.apply x x x = Real.sqrt c *
      (⟪a, x⟫ ^ 3 - 3 * ⟪a, x⟫ * ‖x - ⟪a, x⟫ • a‖ ^ 2)) :
    Module.finrank ℝ V = 4 ∧ Fintype.card ι = 4 ∧
      ∀ i, Module.finrank ℝ (d.piece i) = 1 := by
  have heq : h = Real.sqrt c • Reducible.cubic a := by
    apply cubic_eq_of_diagonal_eq
    intro x
    rw [SymmetricCubic.apply_smul, Reducible.cubic_diagonal ha, diagonal]
  let d₀ : Decomposition (Reducible.cubic a) ι :=
    ⟨d.piece, d.nonzero, d.orthogonal, d.exhaustive, fun i => by
      apply (isClosedPiece_smul_iff (Real.sqrt_pos.mpr round.positive).ne' _).mp
      simpa only [← heq] using d.closed i⟩
  obtain ⟨hv, hi, w, hw, _⟩ := Reducible.four_lines ha d₀ proper
  refine ⟨hv, hi, fun i => ?_⟩
  change Module.finrank ℝ (d₀.piece i) = 1
  rw [(hw i).2.2]
  apply finrank_span_singleton
  intro hz
  have hinner := congrArg (fun x : V => ⟪a, x⟫) hz
  simp only [inner_add_right, real_inner_smul_right, (hw i).2.1,
    real_inner_self_eq_norm_sq, ha, inner_zero_right] at hinner
  norm_num at hinner

/-- Every proper closed orthogonal decomposition has one of the four round patterns. -/
/- The nonharmonic branch uses the proved axial alternative from Vladimir Tkachev's
cubic eikonal classification (arXiv:1001.2387v2, Theorem 1.1). The harmonic branch
uses the separate closed-decomposition classification for harmonic cubics. -/
theorem classifyRoundDecompositions {c : ℝ}
    (d : Decomposition h ι) (round : IsRound h c) (proper : 1 < Fintype.card ι) :
    RoundDecompositionPattern c d := by
  classical
  by_cases harmonic : h.TraceFree
  · exact Or.inr ⟨harmonic, classifyHarmonicRoundDecompositions d round harmonic proper⟩
  · obtain ⟨_, a, ha, hdiag⟩ := tkachevNonharmonic h c round harmonic
    have hpat := reducible_dimension_pattern round d proper ha (fun x => by
      have hs : ⟪a, x⟫ = ⟪x, a⟫ := by apply real_inner_comm
      rw [hs]
      exact hdiag x)
    exact Or.inl ⟨hpat.1, harmonic, hpat.2⟩

omit [FiniteDimensional ℝ V] in
private theorem reducible_round {a : V} (ha : ‖a‖ = 1) : IsRound (Reducible.cubic a) 1 := by
  refine ⟨by norm_num, fun x => ?_⟩
  change ‖(Reducible.cubic a).L x x‖ ^ 2 = _
  rw [Reducible.cubic_square, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x a, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha, mul_one]
  ring

private theorem reducible_not_harmonic {a : V} (ha : ‖a‖ = 1)
    (dim : Module.finrank ℝ V = 4) : ¬ (Reducible.cubic a).TraceFree := by
  intro tf
  have hmul : (Reducible.cubic a).L a =
      (2 : ℝ) • ((innerSL ℝ a).toLinearMap.smulRight a) - LinearMap.id := by
    ext y
    change (4 * ⟪a, a⟫ * ⟪a, y⟫ - ⟪a, y⟫) • a -
        ⟪a, a⟫ • y - ⟪a, y⟫ • a = (2 : ℝ) • (⟪a, y⟫ • a) - y
    rw [real_inner_self_eq_norm_sq, ha]
    norm_num
    module
  have he := tf a
  rw [hmul, map_sub, map_smul, LinearMap.trace_smulRight, LinearMap.trace_id, dim] at he
  change (2 : ℝ) * ⟪a, a⟫ - 4 = 0 at he
  rw [real_inner_self_eq_norm_sq, ha] at he
  norm_num at he

private theorem four_lines_witness :
    ∃ (g : SymmetricCubic (EuclideanSpace ℝ (Fin 4))) (d : Decomposition g (Fin 4)),
      IsRound g 1 ∧ FourLinePattern d := by
  let W := EuclideanSpace ℝ (Fin 4)
  have dim : Module.finrank ℝ W = 4 := by simp [W]
  obtain ⟨a, ha⟩ := exists_norm_eq W (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨d⟩ := Reducible.exists_four_lines ha dim
  have round := reducible_round ha
  have proper : 1 < Fintype.card (Fin 4) := by norm_num
  have pat := reducible_dimension_pattern round d proper ha (fun x => by
    rw [Real.sqrt_one, one_mul, Reducible.cubic_diagonal ha])
  exact ⟨Reducible.cubic a, d, round, pat.1, reducible_not_harmonic ha dim, pat.2⟩

private theorem complex_round : IsRound complexCartanCubic 1 := by
  refine ⟨by norm_num, fun x => ?_⟩
  rw [complexCartanCubic, SymmetricCubic.squareMap_smul, norm_smul, mul_pow,
    Real.norm_of_nonneg (Real.sqrt_nonneg 6), Real.sq_sqrt (by norm_num),
    matrixEqualCubic_squareMap, TracelessHermitian3.square_norm_sq]
  ring

private theorem complex_dim : Module.finrank ℝ TracelessHermitian3 = 8 := by
  rw [← complexCartanEquiv.finrank_eq]
  norm_num [Module.finrank_prod, Complex.finrank_real_complex]

private theorem planes_traceFree (d : Decomposition h ι) {c : ℝ} (round : IsRound h c)
    (dims : ∀ i, Module.finrank ℝ (d.piece i) = 2) : h.TraceFree := by
  let P : PlaneDecomposition V ι := ⟨d.piece, dims, d.orthogonal, d.exhaustive⟩
  exact traceFree_of_isClosedPlaneSystem (planes := P) round d.closed

private theorem nativeNormalization : (Real.sqrt (1 / 6 : ℝ))⁻¹ = Real.sqrt 6 := by
  rw [← Real.sqrt_inv]
  congr 1
  norm_num

private theorem nativeCartan_eq_normalize :
    unitNormalize nativeEqualCubic (1 / 6) = nativeCartanCubic := by
  rw [unitNormalize, nativeNormalization, nativeCartanCubic]

private theorem nativeCartan_round : IsRound nativeCartanCubic 1 := by
  rw [← nativeCartan_eq_normalize]
  exact unitNormalize_isRound Graded.nativeRound

private theorem nativeCartan_traceFree : nativeCartanCubic.TraceFree := by
  rw [← nativeCartan_eq_normalize]
  exact unitNormalize_traceFree
    (traceFree_of_isClosedPlaneSystem Graded.nativeRound Graded.labelledClosedPlanes)

private theorem sqrt_nativeStrength_ne_zero : Real.sqrt (1 / 6 : ℝ) ≠ 0 :=
  (Real.sqrt_pos.mpr (by norm_num)).ne'

/-- All four cases occur at strength one on the indicated Euclidean and native carriers. -/
theorem roundDecompositionRealizations :
    (∃ (g : SymmetricCubic (EuclideanSpace ℝ (Fin 4))) (d : Decomposition g (Fin 4)),
      IsRound g 1 ∧ FourLinePattern d) ∧
    (∃ d : Decomposition complexCartanCubic (Fin 4), IsRound complexCartanCubic 1 ∧
      complexCartanCubic.TraceFree ∧ Module.finrank ℝ TracelessHermitian3 = 8 ∧
      ∀ i, Module.finrank ℝ (d.piece i) = 2) ∧
    (∃ d : Decomposition nativeCartanCubic (Fin 13), IsRound nativeCartanCubic 1 ∧
      nativeCartanCubic.TraceFree ∧ Module.finrank ℝ NativeTraceless = 26 ∧
      ∀ i, Module.finrank ℝ (d.piece i) = 2) ∧
    (∃ d : Decomposition nativeCartanCubic (Fin 10), IsRound nativeCartanCubic 1 ∧
      nativeCartanCubic.TraceFree ∧ Module.finrank ℝ NativeTraceless = 26 ∧
      Module.finrank ℝ (d.piece 0) = 8 ∧
      (∀ i, i ≠ 0 → Module.finrank ℝ (d.piece i) = 2) ∧
      ∃ I : d.piece 0 ≃ₗᵢ[ℝ] TracelessHermitian3,
        nativeCartanCubic.pullback (d.piece 0).subtype =
          complexCartanCubic.pullback (W := ↥(d.piece 0)) I.toLinearMap) := by
  refine ⟨four_lines_witness, ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := exists_complex_four_plane_decomposition
    exact ⟨d, complex_round, planes_traceFree d complex_round hd, complex_dim, hd⟩
  · obtain ⟨d, hd⟩ := exists_nativeAlbert_thirteen_plane_decomposition
    exact ⟨d.smul (show Real.sqrt 6 ≠ 0 by positivity), nativeCartan_round,
      nativeCartan_traceFree, nativeTraceless_finrank, hd⟩
  · obtain ⟨d, h₈, h₂, I, hI⟩ := exists_nativeAlbert_octet_nine_planes
    let D : Decomposition nativeCartanCubic (Fin 10) :=
      d.smul (show Real.sqrt 6 ≠ 0 by positivity)
    have restricted :
        nativeCartanCubic.pullback (d.piece 0).subtype =
          complexCartanCubic.pullback (W := ↥(d.piece 0)) I.toLinearMap := by
      rw [nativeCartanCubic, ← nativeNormalization, pullback_smul_cubic, hI, smul_smul,
        inv_mul_cancel₀ sqrt_nativeStrength_ne_zero, one_smul]
    exact ⟨D, nativeCartan_round, nativeCartan_traceFree, nativeTraceless_finrank,
      h₈, h₂, I, restricted⟩

end

end ThirteenPlanes.ClosedBlocks
