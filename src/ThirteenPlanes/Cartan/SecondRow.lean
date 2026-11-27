module

public import ThirteenPlanes.Cartan.JordanOperators

@[expose] public section

set_option backward.privateInPublic true

/-! The real second-row operator space inside the complex endomorphisms of the Jordan algebra. -/

namespace ThirteenPlanes.Cartan
open scoped RealInnerProductSpace TensorProduct

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- Multiplication operators of two orthogonal idempotents commute on the entire Jordan algebra.
Apply the Jordan identity to their difference; its square is their sum. -/
theorem orthogonal_idempotents_leftMul_commute (M : TraceJordanData J) (p q : J)
    (hp : M.L p p = p) (hq : M.L q q = q) (hpq : M.L p q = 0) :
    Commute (M.L p) (M.L q) := by
  have hqp : M.L q p = 0 := (M.comm q p).trans hpq
  have hsq : M.L (p - q) (p - q) = p + q := by
    simp only [map_sub, LinearMap.sub_apply, hp, hq, hpq, hqp, sub_zero, zero_sub, sub_neg_eq_add]
  have he := M.jordan (p - q)
  rw [hsq, map_sub, map_add] at he
  change (M.L p - M.L q) * (M.L p + M.L q) =
    (M.L p + M.L q) * (M.L p - M.L q) at he
  change M.L p * M.L q = M.L q * M.L p
  simp only [sub_mul, mul_sub, mul_add, add_mul] at he
  have hd : (2 : ℝ) • (M.L p * M.L q - M.L q * M.L p) = 0 := by
    rw [two_smul]
    calc
      _ = (M.L p * M.L p - M.L q * M.L p + (M.L p * M.L q - M.L q * M.L q)) -
          (M.L p * M.L p + M.L q * M.L p - (M.L p * M.L q + M.L q * M.L q)) := by abel
      _ = 0 := sub_eq_zero.mpr he
  exact sub_eq_zero.mp ((smul_eq_zero.mp hd).resolve_left (by norm_num))

private theorem baseChange_add_I_linear (A B : Module.End ℝ J) (r : ℝ) :
    realImagOperator (r • A) (r • B) = r • realImagOperator A B := by
  simp only [realImagOperator, LinearMap.baseChange_smul, smul_add]
  rw [smul_comm Complex.I r]

/-- The linear real/imaginary realization of (K\oplus iL(V)) in the actual complex operators. -/
def secondRowEmbed (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    (K × M.traceFree) →ₗ[ℝ] Module.End ℂ (Complexified J) where
  toFun p := realImagOperator p.1.val.val (M.L p.2.val)
  map_add' p q := by
    change realImagOperator (p.1.val.val + q.1.val.val) (M.L (p.2.val + q.2.val)) = _
    simp only [realImagOperator, map_add, LinearMap.baseChange_add, smul_add]
    abel
  map_smul' r p := by
    change realImagOperator (r • p.1.val.val) (M.L (r • p.2.val)) = _
    rw [map_smul, baseChange_add_I_linear]
    rfl

theorem secondRowEmbed_injective (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    Function.Injective (secondRowEmbed M K) := by
  intro p q h
  have he : (p.1.val.val, M.L p.2.val) = (q.1.val.val, M.L q.2.val) :=
    realImagOperator_injective h
  apply Prod.ext
  · exact Subtype.ext (Subtype.ext (congrArg Prod.fst he))
  · exact Subtype.ext (M.L_injective (congrArg Prod.snd he))

/-- The real subspace of literal complex operators. -/
def secondRowSpace (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    Submodule ℝ (Module.End ℂ (Complexified J)) :=
  LinearMap.range (secondRowEmbed M K)

def secondRowCoordinates (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    (K × M.traceFree) ≃ₗ[ℝ] secondRowSpace M K :=
  LinearEquiv.ofInjective (secondRowEmbed M K) (secondRowEmbed_injective M K)

private def flipImaginary (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    (K × M.traceFree) ≃ₗ[ℝ] (K × M.traceFree) where
  toFun z := (z.1, -z.2)
  invFun z := (z.1, -z.2)
  left_inv z := by simp
  right_inv z := by simp
  map_add' x y := by simp [add_comm]
  map_smul' r x := by simp

/-- Real/imaginary conjugation on the actual second row. -/
def secondRowTheta (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    secondRowSpace M K ≃ₗ[ℝ] secondRowSpace M K :=
  (secondRowCoordinates M K).symm.trans
    ((flipImaginary M K).trans (secondRowCoordinates M K))

@[simp] theorem secondRowTheta_coordinates (M : TraceJordanData J)
    (K : Submodule ℝ (SkewOperator J)) (p : K × M.traceFree) :
    secondRowTheta M K (secondRowCoordinates M K p) =
      secondRowCoordinates M K (p.1, -p.2) := by
  simp only [secondRowTheta, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- A specified torus inside the real skew derivations, with its literal traceless common kernel. -/
abbrev representedFixedPlane (M : TraceJordanData J) {K : Submodule ℝ (SkewOperator J)}
    (T : Submodule ℝ K) : Submodule ℝ M.traceFree :=
  M.fixedTraceless (T.map K.subtype)

theorem fixedPlane_iff (M : TraceJordanData J) {K : Submodule ℝ (SkewOperator J)}
    (T : Submodule ℝ K) (x : M.traceFree) :
    x ∈ representedFixedPlane M T ↔ ∀ D : T, D.val.val.val x.val = 0 := by
  rw [TraceJordanData.mem_fixedTraceless]
  constructor
  · intro hx D
    exact hx ⟨D.val.val, ⟨D.val, D.property, rfl⟩⟩
  · rintro hx ⟨D, W, hW, rfl⟩
    exact hx ⟨W, hW⟩

/-- The second-row mixed centralizer consists exactly of the real centralizer and the
imaginary left multiplication operators of the common-kernel plane. -/
theorem secondRow_centralizer_iff (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))
    (hK : K ≤ M.skewDerivations) (T : Submodule ℝ K)
    (selfCent : ∀ D : K,
      (∀ H : T, operatorBracket H.val.val.val D.val.val = 0) ↔ D ∈ T)
    (p : K × M.traceFree) :
    (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) (secondRowEmbed M K p) = 0) ↔
      p ∈ T.prod (representedFixedPlane M T) := by
  change (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ)
    (realImagOperator p.1.val.val (M.L p.2.val)) = 0) ↔
    p.1 ∈ T ∧ p.2 ∈ representedFixedPlane M T
  rw [← selfCent p.1, fixedPlane_iff]
  constructor
  · intro h
    have hh (H : T) := h H
    simp only [operatorBracket_baseChange_realImag, realImagOperator_eq_zero] at hh
    refine ⟨fun H => (hh H).1, fun H => ?_⟩
    have hD : M.IsDerivation H.val.val.val := hK H.val.property
    have he := (hh H).2
    rw [M.bracket_leftMul hD] at he
    exact M.L_injective (by simpa only [map_zero] using he)
  · rintro ⟨hδ, hx⟩ H
    rw [operatorBracket_baseChange_realImag, realImagOperator_eq_zero]
    exact ⟨hδ H, by rw [M.bracket_leftMul (hK H.val.property), hx H, map_zero]⟩

/-- The actual second-row space attached to one derivation subspace. -/
def secondRowPiece (M : TraceJordanData J) {K : Submodule ℝ (SkewOperator J)}
    (T : Submodule ℝ K) : Submodule ℝ (Module.End ℂ (Complexified J)) :=
  (T.prod (representedFixedPlane M T)).map (secondRowEmbed M K)

end

end ThirteenPlanes.Cartan
