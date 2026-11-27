/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRowMetric

@[expose] public section

set_option backward.privateInPublic true

/-! Conjugation on the actual second-row endomorphisms respects their commutator and trace. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))

theorem secondRowTheta_involutive : Function.Involutive (secondRowTheta M K) := by
  intro X
  obtain ⟨p, rfl⟩ := (secondRowCoordinates M K).surjective X
  simp only [secondRowTheta_coordinates, neg_neg]

theorem secondRowTheta_fixed_iff_real (X : secondRowSpace M K) :
    secondRowTheta M K X = X ↔ ∃ k : K, X = secondRowCoordinates M K (k, 0) := by
  let e := secondRowCoordinates M K
  obtain ⟨p, rfl⟩ := e.surjective X
  constructor
  · intro h
    change secondRowTheta M K (secondRowCoordinates M K p) = secondRowCoordinates M K p at h
    rw [secondRowTheta_coordinates] at h
    have hn : -p.2 = p.2 := congrArg Prod.snd (e.injective h)
    have hh : (2 : ℝ) • p.2 = 0 := by
      rw [two_smul]
      exact (congrArg (fun y => y + p.2) hn.symm).trans (neg_add_cancel p.2)
    have hz : p.2 = 0 := (smul_eq_zero.mp hh).resolve_left (by norm_num)
    exact ⟨p.1, congrArg e (Prod.ext rfl hz)⟩
  · rintro ⟨k, h⟩
    rw [h, secondRowTheta_coordinates, neg_zero]

private theorem realImagProduct (A B C D : Module.End ℝ J) :
    realImagOperator A B * realImagOperator C D = realImagOperator (A * C - B * D) (A * D + B * C) := by
  have hs (U V : Module.End ℝ J) : (U - V).baseChange ℂ = U.baseChange ℂ - V.baseChange ℂ :=
    map_sub (Module.End.baseChangeHom ℝ ℂ J) U V
  simp only [realImagOperator, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, neg_one_smul, LinearMap.baseChange_add, LinearMap.baseChange_mul, hs, smul_add]
  abel

private theorem realImagBracket (A B C D : Module.End ℝ J) :
    operatorBracket (realImagOperator A B) (realImagOperator C D) =
      realImagOperator (operatorBracket A C - operatorBracket B D) (operatorBracket A D + operatorBracket B C) := by
  have hs (U V : Module.End ℝ J) : (U - V).baseChange ℂ = U.baseChange ℂ - V.baseChange ℂ :=
    map_sub (Module.End.baseChangeHom ℝ ℂ J) U V
  rw [operatorBracket, realImagProduct, realImagProduct]
  simp only [realImagOperator, operatorBracket, LinearMap.baseChange_add, hs, smul_add, smul_sub]
  abel

/-- In a bracket-closed second row, conjugation is a Lie automorphism for the actual
operator commutator. This equality can be used before introducing the Lie subtype. -/
theorem secondRowTheta_preserves_operatorBracket (X Y Z : secondRowSpace M K)
    (hZ : Z.val = operatorBracket X.val Y.val) :
    (secondRowTheta M K Z).val =
      operatorBracket (secondRowTheta M K X).val (secondRowTheta M K Y).val := by
  obtain ⟨p, rfl⟩ := (secondRowCoordinates M K).surjective X
  obtain ⟨q, rfl⟩ := (secondRowCoordinates M K).surjective Y
  obtain ⟨r, rfl⟩ := (secondRowCoordinates M K).surjective Z
  change realImagOperator r.1.val.val (M.L r.2.val) =
    operatorBracket (realImagOperator p.1.val.val (M.L p.2.val)) (realImagOperator q.1.val.val (M.L q.2.val)) at hZ
  rw [realImagBracket] at hZ
  have parts : (r.1.val.val, M.L r.2.val) =
      (operatorBracket p.1.val.val q.1.val.val - operatorBracket (M.L p.2.val) (M.L q.2.val),
       operatorBracket p.1.val.val (M.L q.2.val) + operatorBracket (M.L p.2.val) q.1.val.val) :=
    realImagOperator_injective hZ
  simp only [secondRowTheta_coordinates]
  change realImagOperator r.1.val.val (M.L (-r.2.val)) = operatorBracket
    (realImagOperator p.1.val.val (M.L (-p.2.val))) (realImagOperator q.1.val.val (M.L (-q.2.val)))
  rw [realImagBracket]
  have hR := congrArg Prod.fst parts
  have hI := congrArg Prod.snd parts
  dsimp only at hR hI
  rw [map_neg, map_neg, map_neg, hR, hI]
  simp only [operatorBracket, neg_mul, mul_neg]
  congr 1 <;> abel

variable [FiniteDimensional ℝ J]

theorem secondRowTheta_preserves_traceForm (X Y : secondRowSpace M K) :
    complexTraceForm (secondRowTheta M K X).val (secondRowTheta M K Y).val = complexTraceForm X.val Y.val := by
  obtain ⟨p, rfl⟩ := (secondRowCoordinates M K).surjective X
  obtain ⟨q, rfl⟩ := (secondRowCoordinates M K).surjective Y
  simp only [secondRowTheta_coordinates]
  change complexTraceForm (secondRowEmbed M K (p.1, -p.2)) (secondRowEmbed M K (q.1, -q.2)) =
    complexTraceForm (secondRowEmbed M K p) (secondRowEmbed M K q)
  rw [secondRow_traceForm, secondRow_traceForm]
  simp

end

end ThirteenPlanes.Cartan
