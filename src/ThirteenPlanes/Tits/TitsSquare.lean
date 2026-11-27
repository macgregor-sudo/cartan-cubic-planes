/- SPDX-License-Identifier: Apache-2.0
Ported from AlbertLean/Generic/TitsSquare.lean at dd06ef5d423a0e4a5d814d2c221e999b98887ee1. Module imports adapted for Lean 4.36. -/
module

public import ThirteenPlanes.Tits.TitsLinear
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.privateInPublic true

/-! Transport of the first Tits square and polarized product to Tau Ceti coordinates. -/

noncomputable section
namespace AlbertLean.Generic.TitsSquare

open C1Coordinates TitsLinear

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

attribute [local simp] Matrix.vec3_dotProduct cross_apply
  Matrix.vecHead Matrix.vecTail

/-- Cancel the scalar half before expanding any product coordinates. -/
private theorem invOf_two_smul_add_self
    {V : Type*} [AddCommMonoid V] [Module R V] (v : V) :
    ⅟(2 : R) • (v + v) = v := by
  rw [← two_smul R v, smul_smul, invOf_mul_self, one_smul]

/-- Tau's off-diagonal square has no half coefficients after its duplicated
summands are combined. -/
private theorem square_offDiag (x : Albert R) (i : Fin 3) :
    (x * x).offDiag i =
      (x.diag (i + 1) + x.diag (i + 2)) • x.offDiag i +
        TauCeti.Octonion.conj (x.offDiag (i + 1) * x.offDiag (i + 2)) := by
  rw [TauCeti.AlbertAlgebra.mul_offDiag,
    invOf_two_smul_add_self, invOf_two_smul_add_self]

/-- Expose matrix subtraction only after both matrix indices are present. -/
private theorem matrix_sub_apply (M N : Mat3 R) (i j : Fin 3) :
    (M - N) i j = M i j - N i j := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
/-- The exported first-Tits square agrees coordinatewise with Tau's square. -/
theorem toTau_firstTitsSquare (z : FirstTits R) :
    toTau (R := R) (firstTitsSquare z) = toTau z * toTau z := by
  rcases z with ⟨A, B, C⟩
  apply TauCeti.AlbertAlgebra.ext
  · funext i
    fin_cases i <;>
      simp [toTau, toTauRaw, firstTitsSquare, trace3, adjugate3,
        TauCeti.AlbertAlgebra.mul_diag,
        QuadraticMap.associated_eq_self_apply,
        TauCeti.Octonion.norm_def, Matrix.mul_apply,
        Fin.sum_univ_succ, dotProduct] <;> ring
  · funext i
    rw [square_offDiag]
    fin_cases i
    all_goals apply TauCeti.Octonion.ext
    all_goals try (funext j; fin_cases j)
    all_goals
      simp [toTau, toTauRaw, firstTitsSquare, trace3, adjugate3,
        matrix_sub_apply, Matrix.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
        Fin.sum_univ_succ, dotProduct] <;> ring


/-- Any square-preserving linear map transports polarization to Tau product. -/
theorem map_polarProduct
    (square : FirstTits R → FirstTits R)
    (hSquare : ∀ z, toTau (R := R) (square z) = toTau z * toTau z)
    (x y : FirstTits R) :
    toTau (R := R) (polarProduct square x y) = toTau x * toTau y := by
  rw [polarProduct, map_smul, map_sub, map_sub, hSquare, hSquare, hSquare]
  simp only [map_add]
  have hcross :
      (toTau x + toTau y) * (toTau x + toTau y) - toTau x * toTau x -
          toTau y * toTau y =
        toTau x * toTau y + toTau x * toTau y := by
    simp only [add_mul, mul_add]
    rw [mul_comm (toTau y) (toTau x)]
    abel
  rw [hcross, invOf_two_smul_add_self]

theorem toTau_polarProduct (x y : FirstTits R) :
    toTau (R := R) (polarProduct firstTitsSquare x y) =
      toTau x * toTau y :=
  map_polarProduct firstTitsSquare toTau_firstTitsSquare x y


end AlbertLean.Generic.TitsSquare
