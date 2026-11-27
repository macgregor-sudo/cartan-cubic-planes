module

public import ThirteenPlanes.FiniteGroup.Relabel
public import ThirteenPlanes.FiniteGroup.LiftCondition

@[expose] public section

set_option backward.privateInPublic true

/-! The relabeling attached to a determinant-one matrix and an odd phase function, and the
equivalence between preserving the coupling table and the lifting condition. -/

open Matrix

namespace ThirteenPlanes

noncomputable section

namespace FiniteGroup

theorem chargePhase_injective : Function.Injective chargePhase := by
  intro a b hab
  apply ZMod.val_injective
  have hm : a.val < 3 := ZMod.val_lt a
  have hn : b.val < 3 := ZMod.val_lt b
  have him := congrArg Complex.im hab
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  simp only [chargePhase] at him
  generalize a.val = m at *
  generalize b.val = n at *
  interval_cases m <;> interval_cases n <;> first
    | rfl
    | (simp [chargeRoot_sq_eq_star] at him; linarith)
    | (simp [chargeRoot_sq_eq_star] at him)

private theorem three_eq_zero : (3 : ZMod 3) = 0 := by decide

variable (A : SpecialLinearGroup (Fin 3) (ZMod 3))

theorem mulVec_inv_mulVec (x : Charge) :
    ((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 3)) : ChargeMatrix) *ᵥ ((A : ChargeMatrix) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (x : Charge) :
    (A : ChargeMatrix) *ᵥ (((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 3)) : ChargeMatrix) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
    SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVec_injective : Function.Injective ((A : ChargeMatrix) *ᵥ ·) := by
  intro x y h
  have := congrArg (((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 3)) : ChargeMatrix) *ᵥ ·) h
  simpa only [mulVec_inv_mulVec] using this

theorem mulVec_ne_zero {x : Charge} (hx : x ≠ 0) : (A : ChargeMatrix) *ᵥ x ≠ 0 := by
  intro h
  apply hx
  apply mulVec_injective A
  simp [h]

/-- The action of a determinant-one matrix on the nonzero grades. -/
def chargeAct : NonzeroCharge ≃ NonzeroCharge where
  toFun x := ⟨(A : ChargeMatrix) *ᵥ x.val, mulVec_ne_zero A x.property⟩
  invFun y := ⟨((A⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 3)) : ChargeMatrix) *ᵥ y.val,
    mulVec_ne_zero A⁻¹ y.property⟩
  left_inv x := Subtype.ext (mulVec_inv_mulVec A x.val)
  right_inv y := Subtype.ext (mulVec_mulVec_inv A y.val)

@[simp] theorem chargeAct_val (x : NonzeroCharge) :
    (chargeAct A x).val = (A : ChargeMatrix) *ᵥ x.val := rfl

/-- The relabeling `u_x ↦ ω^{F(x)} u_{Ax}` of a determinant-one matrix and an odd phase function. -/
def codeRelabeling (F : Charge → ZMod 3) (hF : IsOddPhase F) : Relabeling where
  perm := chargeAct A
  perm_opposite x := Subtype.ext (by
    change (A : ChargeMatrix) *ᵥ (-x.val) = -((A : ChargeMatrix) *ᵥ x.val)
    exact Matrix.mulVec_neg _ _)
  phase x := F x.val
  phase_opposite x := hF x.val

private theorem dependent_mulVec_iff (x y : Charge) :
    dependentGrades ((A : ChargeMatrix) *ᵥ x) ((A : ChargeMatrix) *ᵥ y) ↔ dependentGrades x y := by
  have inj := mulVec_injective A
  have hxy : ∀ u v : Charge, (A : ChargeMatrix) *ᵥ u = (A : ChargeMatrix) *ᵥ v ↔ u = v :=
    fun u v => ⟨fun h => inj h, fun h => by rw [h]⟩
  have h0 : ∀ v : Charge, (A : ChargeMatrix) *ᵥ v = 0 ↔ v = 0 := by
    intro v
    have := hxy v 0
    rwa [Matrix.mulVec_zero] at this
  have hn : (A : ChargeMatrix) *ᵥ x = -((A : ChargeMatrix) *ᵥ y) ↔ x = -y := by
    rw [← Matrix.mulVec_neg, hxy]
  unfold dependentGrades
  rw [h0, h0, hxy, hn]

private theorem signedCoefficient_independent {x y w : NonzeroCharge}
    (hs : x.val + y.val + w.val = 0) (hd : ¬ dependentGrades x.val y.val) :
    signedCoefficient x y w = -(3 / 2) * chargePhase (gradeExponent x.val y.val) := by
  simp only [signedCoefficient, gradeMetric, hs, ↓reduceIte, gradedProductCoefficient, hd,
    chargePhase]
  ring

/-- Preserving the coupling table is the lifting condition. -/
theorem tableInvariant_iff (F : Charge → ZMod 3) (hF : IsOddPhase F) :
    (codeRelabeling A F hF).TableInvariant ↔ LiftCondition A F := by
  constructor
  · intro h x y hd
    have hx : x ≠ 0 := fun e => hd (Or.inl e)
    have hy : y ≠ 0 := fun e => hd (Or.inr (Or.inl e))
    have hw : -(x + y) ≠ 0 := by
      intro e
      apply hd
      right; right; right
      linear_combination -e
    have e := h ⟨x, hx⟩ ⟨y, hy⟩ ⟨-(x + y), hw⟩
    change chargePhase (F x + F y + F (-(x + y))) *
      signedCoefficient (chargeAct A ⟨x, hx⟩) (chargeAct A ⟨y, hy⟩) (chargeAct A ⟨-(x + y), hw⟩) =
      signedCoefficient ⟨x, hx⟩ ⟨y, hy⟩ ⟨-(x + y), hw⟩ at e
    have hs : x + y + -(x + y) = 0 := by ring
    have hsA : (chargeAct A ⟨x, hx⟩).val + (chargeAct A ⟨y, hy⟩).val +
        (chargeAct A ⟨-(x + y), hw⟩).val = 0 := by
      simp only [chargeAct_val, ← Matrix.mulVec_add, hs, Matrix.mulVec_zero]
    have hdA : ¬ dependentGrades (chargeAct A ⟨x, hx⟩).val (chargeAct A ⟨y, hy⟩).val := by
      simpa only [chargeAct_val, dependent_mulVec_iff] using hd
    rw [signedCoefficient_independent hsA hdA, signedCoefficient_independent hs hd] at e
    simp only [chargeAct_val] at e
    have e2 : chargePhase (F x + F y + F (-(x + y)) +
        gradeExponent ((A : ChargeMatrix) *ᵥ x) ((A : ChargeMatrix) *ᵥ y)) =
        chargePhase (gradeExponent x y) := by
      rw [chargePhase_add]
      linear_combination (-(2 / 3) : ℂ) * e
    have e3 := chargePhase_injective e2
    rw [hF] at e3
    linear_combination e3
  · intro h X Y W
    change chargePhase (F X.val + F Y.val + F W.val) *
      signedCoefficient (chargeAct A X) (chargeAct A Y) (chargeAct A W) = signedCoefficient X Y W
    have hsA : ∀ s : Charge, (chargeAct A X).val + (chargeAct A Y).val + (chargeAct A W).val =
        (A : ChargeMatrix) *ᵥ (X.val + Y.val + W.val) := by
      intro _; simp only [chargeAct_val, Matrix.mulVec_add]
    by_cases hs : X.val + Y.val + W.val = 0
    · by_cases hd : dependentGrades X.val Y.val
      · rcases hd with e | e | e | e
        · exact absurd e X.property
        · exact absurd e Y.property
        · have hXY : X = Y := Subtype.ext e
          have h3c : (3 : Charge) = 0 := by decide
          have hW : W = X := by
            apply Subtype.ext
            rw [← e] at hs
            linear_combination hs - X.val * h3c
          rw [← hXY, hW, signedCoefficient_diagonal, signedCoefficient_diagonal]
          have : F X.val + F X.val + F X.val = 0 := by
            linear_combination F X.val * three_eq_zero
          rw [this, chargePhase_zero, one_mul]
        · exfalso
          apply W.property
          rw [e] at hs
          linear_combination hs
      · have hsA' := hsA 0
        rw [hs, Matrix.mulVec_zero] at hsA'
        have hdA : ¬ dependentGrades (chargeAct A X).val (chargeAct A Y).val := by
          simpa only [chargeAct_val, dependent_mulVec_iff] using hd
        rw [signedCoefficient_independent hsA' hdA, signedCoefficient_independent hs hd]
        have hWv : W.val = -(X.val + Y.val) := by linear_combination hs
        have hl := h X.val Y.val hd
        have e : F X.val + F Y.val + F W.val +
            gradeExponent ((A : ChargeMatrix) *ᵥ X.val) ((A : ChargeMatrix) *ᵥ Y.val) =
            gradeExponent X.val Y.val := by
          rw [hWv, hF]
          linear_combination hl
        have e' := congrArg chargePhase e
        rw [chargePhase_add] at e'
        simp only [chargeAct_val]
        linear_combination (-(3 / 2) : ℂ) * e'
    · have hsA' := hsA 0
      have hnA : (chargeAct A X).val + (chargeAct A Y).val + (chargeAct A W).val ≠ 0 := by
        rw [hsA']; exact mulVec_ne_zero A hs
      rw [signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ hnA,
        signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ hs, mul_zero]

end FiniteGroup

end

end ThirteenPlanes
