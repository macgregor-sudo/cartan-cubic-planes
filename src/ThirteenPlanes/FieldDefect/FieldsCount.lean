module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import ThirteenPlanes.FieldDefect.Statements
public import ThirteenPlanes.Fields.RadialClassification

@[expose] public section

set_option backward.privateInPublic true

/-! The field count used in the positive-defect proposition. -/

open scoped BigOperators

namespace ThirteenPlanes.AlbertGrading.Defect

noncomputable section

private def tripleEquiv (m : ℕ) : Triple m ≃ Fields.IncreasingTriple m where
  toFun t := ⟨(t.val 0, t.val 1, t.val 2), t.property⟩
  invFun t := ⟨![t.val.1, t.val.2.1, t.val.2.2], t.property⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv t := by
    apply Subtype.ext
    rfl

private def curryThree (T : TriForm) : Fields.RealTrilinear :=
  let one := (MultilinearMap.ofSubsingletonₗ (S := ℝ) (RingHom.id ℝ) ℂ ℝ
    (0 : Fin 1)).symm.toLinearMap
  let two := (LinearMap.llcomp ℝ ℂ _ _ one).comp
    (multilinearCurryLeftEquiv (S := ℝ) (RingHom.id ℝ) (fun _ : Fin 2 => ℂ) ℝ).toLinearMap
  two.comp T.curryLeft

private theorem curryThree_apply (T : TriForm) (x y z : ℂ) :
    curryThree T x y z = T ![x, y, z] := by
  change T (Fin.cons x (Fin.cons y (fun _ : Fin 1 => z))) = T ![x, y, z]
  congr 1
  funext i
  fin_cases i <;> rfl

private def curriedCoefficients {m : ℕ} (T : Triple m → TriForm) :
    Fields.IncreasingTriple m → Fields.RealTrilinear :=
  fun t => curryThree (T ((tripleEquiv m).symm t))

private theorem fieldCubic_eq_polynomial {m : ℕ} (T : Triple m → TriForm) :
    fieldCubic T = Fields.polynomial (curriedCoefficients T) := by
  funext z
  unfold fieldCubic Fields.polynomial
  congr 1
  refine Fintype.sum_equiv (tripleEquiv m) _ _ (fun t => ?_)
  simp only [curriedCoefficients, Equiv.symm_apply_apply, curryThree_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The closed-plane classification supplies the exact field-count input for the defect theorem. -/
theorem fieldsCount : FieldClassification.FieldsCount := by
  intro m hm W hW hRadial
  obtain ⟨T, rfl⟩ := hW
  obtain ⟨φ, hφ⟩ := hRadial
  rw [fieldCubic_eq_polynomial T] at hφ
  have hEnergy : Fields.HasRadialFieldEnergy (curriedCoefficients T) := by
    intro x y hxy
    change (gradNorm (Fields.polynomial (curriedCoefficients T)) x) ^ 2 =
      (gradNorm (Fields.polynomial (curriedCoefficients T)) y) ^ 2
    rw [hφ x, hφ y, hxy]
  rcases Fields.field_polynomial_count_and_model hm _ hEnergy with h₁ | ⟨h₄, _⟩ | ⟨h₁₃, _⟩
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₄)
  · exact Or.inr (Or.inr h₁₃)

end

end ThirteenPlanes.AlbertGrading.Defect
