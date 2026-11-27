module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option backward.privateInPublic true

/-! Exponential transport, invariant subspaces, and conjugation by an exponential. -/

namespace ThirteenPlanes.Cartan

open NormedSpace

noncomputable section

section Operators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exp_apply_hasSum (A : E →L[ℝ] E) (x : E) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (A ^ n) x) (exp A x) := by
  let ev := ContinuousLinearMap.apply ℝ E x
  simpa only [Function.comp_def, map_smul, ev, ContinuousLinearMap.apply_apply] using
    (exp_series_hasSum_exp' (𝕂 := ℝ) A).map ev ev.continuous

/-- An intertwiner of two endomorphisms intertwines their exponentials. -/
theorem intertwines_exp (f : E →L[ℝ] F) (A : E →L[ℝ] E) (B : F →L[ℝ] F)
    (intertwines : ∀ x, f (A x) = B (f x)) (x : E) : f (exp A x) = exp B (f x) := by
  have hp (n : ℕ) : f ((A ^ n) x) = (B ^ n) (f x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change f (A ((A ^ n) x)) = B ((B ^ n) (f x))
      rw [intertwines, ih]
  have hs := (exp_apply_hasSum A x).map f f.continuous
  simp only [Function.comp_def, map_smul, hp] at hs
  exact hs.unique (exp_apply_hasSum B (f x))

theorem exp_mem_of_invariant [FiniteDimensional ℝ E] (S : Submodule ℝ E) (A : E →L[ℝ] E)
    (stable : ∀ x ∈ S, A x ∈ S) {x : E} (hx : x ∈ S) : exp A x ∈ S := by
  have hp (n : ℕ) : (A ^ n) x ∈ S := by
    induction n with
    | zero => exact hx
    | succ n ih =>
      rw [pow_succ']
      exact stable _ ih
  apply S.isClosed_of_finiteDimensional.mem_of_tendsto (exp_apply_hasSum A x)
  exact Filter.Eventually.of_forall fun _ => S.sum_mem (fun n _ => S.smul_mem _ (hp n))

end Operators

section Algebra

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

local instance : NormedAlgebra ℚ R := NormedAlgebra.restrictScalars ℚ ℝ _
local instance : NormedAlgebra ℚ (R →L[ℝ] R) := NormedAlgebra.restrictScalars ℚ ℝ _

private theorem exp_leftMultiplication (a x : R) :
    exp (ContinuousLinearMap.mul ℝ R a) x = exp a * x := by
  let L := ContinuousLinearMap.mul ℝ R a
  let f := (ContinuousLinearMap.mul ℝ R).flip x
  have hp (n : ℕ) : (L ^ n) x = a ^ n * x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change a * ((L ^ n) x) = a * a ^ n * x
      rw [ih, mul_assoc]
  have hs := exp_apply_hasSum L x
  simp only [hp] at hs
  have hr := (exp_series_hasSum_exp' (𝕂 := ℝ) a).map f f.continuous
  simp only [Function.comp_def, map_smul, f, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply'] at hr
  exact hs.unique hr

private theorem exp_rightMultiplication (a x : R) :
    exp ((ContinuousLinearMap.mul ℝ R).flip a) x = x * exp a := by
  let R' := (ContinuousLinearMap.mul ℝ R).flip a
  let f := ContinuousLinearMap.mul ℝ R x
  have hp (n : ℕ) : (R' ^ n) x = x * a ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ]
      change (R' ^ n) x * a = x * (a ^ n * a)
      rw [ih, mul_assoc]
  have hs := exp_apply_hasSum R' x
  simp only [hp] at hs
  have hr := (exp_series_hasSum_exp' (𝕂 := ℝ) a).map f f.continuous
  simp only [Function.comp_def, map_smul, f, ContinuousLinearMap.mul_apply'] at hr
  exact hs.unique hr

/-- The adjoint operator on a real normed algebra, given by its literal commutator. -/
def commutatorOperator (a : R) : R →L[ℝ] R :=
  ContinuousLinearMap.mul ℝ R a - (ContinuousLinearMap.mul ℝ R).flip a

omit [CompleteSpace R] in
theorem commutatorOperator_apply (a x : R) : commutatorOperator a x = a * x - x * a := rfl

/-- Exponentiating the commutator gives conjugation by the algebra exponential. -/
theorem exp_commutatorOperator (a x : R) : exp (commutatorOperator a) x = exp a * x * exp (-a) := by
  let L := ContinuousLinearMap.mul ℝ R a
  let R' := (ContinuousLinearMap.mul ℝ R).flip a
  have comm : Commute L R' := by ext y; exact (mul_assoc a y a).symm
  change exp (L - R') x = _
  rw [sub_eq_add_neg, exp_add_of_commute comm.neg_right]
  change exp L (exp (-R') x) = _
  rw [show -R' = (ContinuousLinearMap.mul ℝ R).flip (-a) from (map_neg _ a).symm,
    exp_rightMultiplication, exp_leftMultiplication, mul_assoc]

end Algebra

end

end ThirteenPlanes.Cartan
