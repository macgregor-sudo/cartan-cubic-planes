/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Reducible.FourLines

@[expose] public section

set_option backward.privateInPublic true

/-! The reducible case at arbitrary strength and its four-dimensional witness. -/

open scoped RealInnerProductSpace

namespace Challenge.Bridge

open ThirteenPlanes ThirteenPlanes.RoundCubics

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem reducible_dimension_pattern {ι : Type*} [Fintype ι] {h : SymmetricCubic V}
    {c : ℝ} (hr : IsRound h c) (d : ClosedBlocks.Decomposition h ι)
    (proper : 1 < Fintype.card ι) {a : V} (ha : ‖a‖ = 1)
    (diagonal : ∀ x : V, h.apply x x x = Real.sqrt c *
      (⟪a, x⟫ ^ 3 - 3 * ⟪a, x⟫ * ‖x - ⟪a, x⟫ • a‖ ^ 2)) :
    Module.finrank ℝ V = 4 ∧ Fintype.card ι = 4 ∧
      ∀ i, Module.finrank ℝ (d.piece i) = 1 := by
  have heq : h = Real.sqrt c • Reducible.cubic a := by
    apply Peirce.cubic_eq_of_diagonal_eq
    intro x
    rw [SymmetricCubic.apply_smul, Reducible.cubic_diagonal ha, diagonal]
  let d₀ : ClosedBlocks.Decomposition (Reducible.cubic a) ι :=
    ⟨d.piece, d.nonzero, d.orthogonal, d.exhaustive, fun i => by
      apply (isClosedPiece_smul_iff (Real.sqrt_pos.mpr hr.positive).ne' _).mp
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

omit [FiniteDimensional ℝ V] in
private theorem reducible_round {a : V} (ha : ‖a‖ = 1) : IsRound (Reducible.cubic a) 1 := by
  refine ⟨by norm_num, fun x => ?_⟩
  change ‖(Reducible.cubic a).L x x‖ ^ 2 = _
  rw [Reducible.cubic_square, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x a, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha, mul_one]
  ring

private theorem reducible_not_harmonic {a : V} (ha : ‖a‖ = 1)
    (hd : Module.finrank ℝ V = 4) : ¬ (Reducible.cubic a).TraceFree := by
  intro tf
  have h : (Reducible.cubic a).L a =
      (2 : ℝ) • ((innerSL ℝ a).toLinearMap.smulRight a) - LinearMap.id := by
    ext y
    change (4 * ⟪a, a⟫ * ⟪a, y⟫ - ⟪a, y⟫) • a -
        ⟪a, a⟫ • y - ⟪a, y⟫ • a = (2 : ℝ) • (⟪a, y⟫ • a) - y
    rw [real_inner_self_eq_norm_sq, ha]
    norm_num
    module
  have he := tf a
  rw [h, map_sub, map_smul, LinearMap.trace_smulRight, LinearMap.trace_id, hd] at he
  change (2 : ℝ) * ⟪a, a⟫ - 4 = 0 at he
  rw [real_inner_self_eq_norm_sq, ha] at he
  norm_num at he

theorem four_lines_witness : ∃ (h : SymmetricCubic (EuclideanSpace ℝ (Fin 4)))
    (d : ClosedBlocks.Decomposition h (Fin 4)), IsRound h 1 ∧ ¬ h.TraceFree ∧
      ∀ i, Module.finrank ℝ (d.piece i) = 1 := by
  let W := EuclideanSpace ℝ (Fin 4)
  have hd : Module.finrank ℝ W = 4 := by simp [W]
  obtain ⟨a, ha⟩ := exists_norm_eq W (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨d⟩ := Reducible.exists_four_lines ha hd
  have h := reducible_round ha
  have hp : 1 < Fintype.card (Fin 4) := by norm_num
  refine ⟨Reducible.cubic a, d, h, reducible_not_harmonic ha hd, ?_⟩
  exact (reducible_dimension_pattern h d hp ha (fun x => by
    rw [Real.sqrt_one, one_mul, Reducible.cubic_diagonal ha])).2.2

end

end Challenge.Bridge
