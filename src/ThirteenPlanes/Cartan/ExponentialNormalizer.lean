module

public import ThirteenPlanes.Cartan.OperatorExponential
public import ThirteenPlanes.Cartan.JordanExponential

@[expose] public section

/-! Restriction and normalization for the exponential of a Jordan derivation. -/

namespace ThirteenPlanes.Cartan

open NormedSpace

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

local instance : NormedAlgebra ℚ R := NormedAlgebra.restrictScalars ℚ ℝ _

/-- A subspace stable under commutation by an element is normalized by its exponential. -/
theorem exp_normalizes_of_commutator [FiniteDimensional ℝ R] (S : Submodule ℝ R) (a : R)
    (stable : ∀ x ∈ S, a * x - x * a ∈ S) :
    (fun x => exp a * x * exp (-a)) '' (S : Set R) = S := by
  have preserves {d : R} (hd : ∀ x ∈ S, d * x - x * d ∈ S) {x} (hx : x ∈ S) :
      exp d * x * exp (-d) ∈ S := by
    rw [← exp_commutatorOperator]
    exact exp_mem_of_invariant S (commutatorOperator d) hd hx
  have hneg (x) (hx : x ∈ S) : (-a) * x - x * (-a) ∈ S := by
    rw [show (-a) * x - x * (-a) = -(a * x - x * a) by rw [neg_mul, mul_neg]; abel]
    exact S.neg_mem (stable x hx)
  have inverse : exp a * exp (-a) = 1 := by
    rw [← exp_add_of_commute (Commute.refl a).neg_right, add_neg_cancel, exp_zero]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact preserves stable hy
  · intro hx
    have he : exp (-a) * x * exp a ∈ S := by simpa only [neg_neg] using preserves hneg hx
    refine ⟨exp (-a) * x * exp a, he, ?_⟩
    calc
      exp a * (exp (-a) * x * exp a) * exp (-a) =
          (exp a * exp (-a)) * x * (exp a * exp (-a)) := by simp only [mul_assoc]
      _ = x := by rw [inverse, one_mul, mul_one]

namespace TraceJordanData

variable {J Q : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  (M : TraceJordanData J)

/-- If the restriction of a derivation is a matrix commutator in the given coordinates,
its exponential on that algebra is the literal conjugation by the matrix exponential. -/
theorem expAutomorphism_on_inner_action (D : M.skewDerivations) (i : Q →L[ℝ] J)
    (ψ : Q →L[ℝ] R) (B : Q →L[ℝ] Q) (a : R)
    (restriction : ∀ x, i (B x) = D.val.val (i x))
    (innerAction : ∀ x, ψ (B x) = a * ψ x - ψ x * a) (x : Q) :
    (M.expAutomorphism D).action (i x) = i (exp B x) ∧
      ψ (exp B x) = exp a * ψ x * exp (-a) := by
  let : CompleteSpace J := FiniteDimensional.completeSpace ℝ J
  refine ⟨?_, ?_⟩
  · rw [M.expAutomorphism_apply]
    exact (intertwines_exp i B (LinearMap.toContinuousLinearMap D.val.val) restriction x).symm
  · rw [← exp_commutatorOperator]
    exact intertwines_exp ψ B (commutatorOperator a) innerAction x

end TraceJordanData

end

end ThirteenPlanes.Cartan
