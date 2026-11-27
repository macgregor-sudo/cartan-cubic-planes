/- SPDX-License-Identifier: Apache-2.0
Ported from AlbertLean/Generic/TitsLinear.lean at dd06ef5d423a0e4a5d814d2c221e999b98887ee1. Module imports adapted for Lean 4.36. -/
module

public import ThirteenPlanes.Tits.C1Coordinates
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Linear identification of the first Tits and Tau Ceti coordinates. -/

noncomputable section
namespace AlbertLean.Generic.TitsLinear

open C1Coordinates

variable {R : Type*}

@[simp] theorem fromTauRaw_toTauRaw [AddCommGroup R] (z : FirstTits R) :
    fromTauRaw (toTauRaw z) = z := by
  rcases z with ⟨A, B, C⟩
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · apply Prod.ext
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [fromTauRaw, toTauRaw]
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem toTauRaw_fromTauRaw [AddCommGroup R] (x : Albert R) :
    toTauRaw (fromTauRaw x) = x := by
  apply TauCeti.AlbertAlgebra.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> apply TauCeti.Octonion.ext <;>
      simp [fromTauRaw, toTauRaw]
    all_goals
      funext j
      fin_cases j <;> simp [fromTauRaw, toTauRaw]

/-- The exported signed coordinate permutation as a linear equivalence. -/
def toTau [CommRing R] : FirstTits R ≃ₗ[R] Albert R where
  toFun := toTauRaw
  invFun := fromTauRaw
  left_inv := fromTauRaw_toTauRaw
  right_inv := toTauRaw_fromTauRaw
  map_add' x y := by
    apply TauCeti.AlbertAlgebra.ext
    · funext i
      fin_cases i <;> simp [toTauRaw]
    · funext i
      fin_cases i <;> apply TauCeti.Octonion.ext <;> simp [toTauRaw]
      all_goals exact ⟨add_comm _ _, add_comm _ _, add_comm _ _⟩
  map_smul' a x := by
    apply TauCeti.AlbertAlgebra.ext
    · funext i
      fin_cases i <;> simp [toTauRaw]
    · funext i
      fin_cases i <;> apply TauCeti.Octonion.ext <;> simp [toTauRaw]

@[simp] theorem toTau_firstTitsOne [CommRing R] :
    toTau (R := R) firstTitsOne = 1 := by
  apply TauCeti.AlbertAlgebra.ext
  · funext i
    fin_cases i <;> simp [toTau, toTauRaw, firstTitsOne]
  · funext i
    fin_cases i <;> apply TauCeti.Octonion.ext <;>
      simp [toTau, toTauRaw, firstTitsOne]

/-- Tau's linear trace reads exactly the trace of the first matrix slot. -/
theorem tauTrace_toTau [CommRing R] (z : FirstTits R) :
    TauCeti.AlbertAlgebra.trace (toTau (R := R) z) = Matrix.trace z.1 := by
  simp [toTau, toTauRaw, TauCeti.AlbertAlgebra.trace_apply,
    Matrix.trace_fin_three, Fin.sum_univ_succ, add_assoc]

theorem trace3_eq_matrixTrace [CommRing R] (A : Mat3 R) :
    trace3 A = Matrix.trace A := by
  rw [Matrix.trace_fin_three]
  rfl

theorem adjugate3_eq_matrixAdjugate [CommRing R] (A : Mat3 R) :
    adjugate3 A = Matrix.adjugate A := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjugate3] <;> ring


end AlbertLean.Generic.TitsLinear
