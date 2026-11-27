module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.privateInPublic true

/-! Real and imaginary endomorphisms inside the literal complexification. -/

namespace ThirteenPlanes.Cartan

open scoped TensorProduct

noncomputable section

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- The complexification used for the second row. -/
abbrev Complexified (J : Type*) [AddCommGroup J] [Module ℝ J] := ℂ ⊗[ℝ] J

private def tensorCoordinate (J : Type*) [AddCommGroup J] [Module ℝ J]
    (f : ℂ →ₗ[ℝ] ℝ) : Complexified J →ₗ[ℝ] J :=
  (TensorProduct.lid ℝ J).toLinearMap.comp (TensorProduct.map f LinearMap.id)

@[simp] private theorem tensorCoordinate_tmul (f : ℂ →ₗ[ℝ] ℝ) (z : ℂ) (x : J) :
    tensorCoordinate J f (z ⊗ₜ[ℝ] x) = f z • x := by
  simp [tensorCoordinate]

/-- The real operator (D+iL) on the actual complexified space. -/
def realImagOperator (D L : Module.End ℝ J) : Module.End ℂ (Complexified J) :=
  D.baseChange ℂ + Complex.I • L.baseChange ℂ

private theorem realImagOperator_one_tmul (D L : Module.End ℝ J) (x : J) :
    realImagOperator D L (1 ⊗ₜ[ℝ] x) = (1 : ℂ) ⊗ₜ[ℝ] D x + Complex.I ⊗ₜ[ℝ] L x := by
  simp [realImagOperator, TensorProduct.smul_tmul']

/-- The real and imaginary parts are separately determined by the complex operator. -/
theorem realImagOperator_injective :
    Function.Injective (fun p : Module.End ℝ J × Module.End ℝ J => realImagOperator p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun h (1 ⊗ₜ[ℝ] x)
    simp only [realImagOperator_one_tmul] at he
    have hr := congrArg (tensorCoordinate J Complex.reLm) he
    simpa [map_add] using hr
  · apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun h (1 ⊗ₜ[ℝ] x)
    simp only [realImagOperator_one_tmul] at he
    have hi := congrArg (tensorCoordinate J Complex.imLm) he
    simpa [map_add] using hi

@[simp] theorem realImagOperator_eq_zero (A B : Module.End ℝ J) :
    realImagOperator A B = 0 ↔ A = 0 ∧ B = 0 := by
  have h0 : realImagOperator (0 : Module.End ℝ J) 0 = 0 := by simp [realImagOperator]
  rw [← h0]
  constructor
  · intro h
    have he : (A, B) = (0, 0) := realImagOperator_injective h
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]

/-- The usual endomorphism commutator. -/
def operatorBracket {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (A B : Module.End R E) : Module.End R E := A * B - B * A

/-- Taking the bracket with a real operator preserves the real/imaginary splitting. -/
theorem operatorBracket_baseChange_realImag (H D L : Module.End ℝ J) :
    operatorBracket (H.baseChange ℂ) (realImagOperator D L) =
      realImagOperator (operatorBracket H D) (operatorBracket H L) := by
  have hs (A B : Module.End ℝ J) : (A - B).baseChange ℂ = A.baseChange ℂ - B.baseChange ℂ :=
    map_sub (Module.End.baseChangeHom ℝ ℂ J) A B
  simp only [realImagOperator, operatorBracket, mul_add, add_mul, smul_mul_assoc,
    mul_smul_comm, hs, LinearMap.baseChange_mul, smul_sub]
  abel

/-- The second-row trace form on the literal complex operator space. -/
def complexTraceForm (A B : Module.End ℂ (Complexified J)) : ℂ :=
  -LinearMap.trace ℂ (Complexified J) (A * B)

theorem complexTraceForm_realImag [FiniteDimensional ℝ J] (A B L M : Module.End ℝ J) :
    complexTraceForm (realImagOperator A L) (realImagOperator B M) =
      ((-LinearMap.trace ℝ J (A * B) + LinearMap.trace ℝ J (L * M) : ℝ) : ℂ) -
      Complex.I * ((LinearMap.trace ℝ J (A * M) + LinearMap.trace ℝ J (L * B) : ℝ) : ℂ) := by
  have hre (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
  simp only [complexTraceForm, realImagOperator, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, ← LinearMap.baseChange_mul, map_add, map_smul, LinearMap.trace_baseChange,
    Complex.ofReal_add, Complex.ofReal_neg, smul_eq_mul, hre, ← mul_assoc,
    Complex.I_mul_I, neg_one_mul]
  ring

end

end ThirteenPlanes.Cartan
