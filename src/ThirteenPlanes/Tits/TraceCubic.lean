/- SPDX-License-Identifier: Apache-2.0
Trace pairing and trace cube adapted from the albert-frame-triple-invariants package,
TitsDetectorIdentities and TitsTraceCube at dd06ef5d423a0e4a5d814d2c221e999b98887ee1. -/
module

public import ThirteenPlanes.Tits.TitsSquare
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace ThirteenPlanes.Tits
open AlbertLean.Generic.C1Coordinates AlbertLean.Generic.TitsLinear AlbertLean.Generic.TitsSquare
variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The full first component of the polarized first-Tits square. -/
theorem polarProduct_firstComponent_full
    (A B C D E F : Mat3 R) :
    (polarProduct firstTitsSquare (A, B, C) (D, E, F)).1 =
      ⅟(2 : R) •
        (A * D + D * A - B * F - E * C +
          (trace3 (B * F) + trace3 (E * C)) • (1 : Mat3 R)) := by
  have ht (X Y : Mat3 R) : trace3 (X + Y) = trace3 X + trace3 Y := by
    simpa only [trace3_eq_matrixTrace] using Matrix.trace_add X Y
  change ⅟(2 : R) •
      (((A + D) * (A + D) - (B + E) * (C + F) +
          trace3 ((B + E) * (C + F)) • (1 : Mat3 R)) -
        (A * A - B * C + trace3 (B * C) • (1 : Mat3 R)) -
        (D * D - E * F + trace3 (E * F) • (1 : Mat3 R))) = _
  simp only [add_mul, mul_add, ht, add_smul]
  congr 1
  abel

/-- The trace pairing of two arbitrary transported first-Tits triples. -/
theorem tauTrace_toTau_mul_toTau
    (A B C D E F : Mat3 R) :
    TauCeti.AlbertAlgebra.trace
        (toTau (R := R) (A, B, C) * toTau (D, E, F)) =
      Matrix.trace (A * D) + Matrix.trace (B * F) + Matrix.trace (C * E) := by
  rw [← toTau_polarProduct, tauTrace_toTau,
    polarProduct_firstComponent_full]
  simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub,
    trace3_eq_matrixTrace, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat]
  have h :
      Matrix.trace (A * D) + Matrix.trace (D * A) -
          Matrix.trace (B * F) - Matrix.trace (E * C) +
          (Matrix.trace (B * F) + Matrix.trace (E * C)) * (3 : R) =
        (2 : R) *
          (Matrix.trace (A * D) + Matrix.trace (B * F) +
            Matrix.trace (C * E)) := by
    rw [Matrix.trace_mul_comm D A, Matrix.trace_mul_comm E C]
    ring
  rw [h, ← mul_assoc, invOf_mul_self, one_mul]

/-- The full bracketed trace cube, obtained from the square and trace pairing.
It requires no separate identification of the Albert cubic norm. -/
theorem tauTrace_cube (A B C : Mat3 R) :
    let x := toTau (R := R) (A, B, C)
    TauCeti.AlbertAlgebra.trace (x * (x * x)) =
      Matrix.trace (A * (A * A)) - 3 * Matrix.trace (A * (B * C)) +
        3 * Matrix.trace A * Matrix.trace (B * C) +
        3 * (Matrix.det B + Matrix.det C) := by
  dsimp only
  rw [← toTau_firstTitsSquare]
  simp only [firstTitsSquare, tauTrace_toTau_mul_toTau, mul_add, mul_sub,
    Matrix.mul_smul, mul_one, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, adjugate3_eq_matrixAdjugate, Matrix.mul_adjugate,
    Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul,
    trace3_eq_matrixTrace]
  have h1 : Matrix.trace (B * (C * A)) = Matrix.trace (A * (B * C)) := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_cycle B C A]
  have h2 : Matrix.trace (C * (A * B)) = Matrix.trace (A * (B * C)) := by
    rw [Matrix.trace_mul_comm C (A * B), Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm C B]
  ring

/-- On traceless matrices the trace cube is three times the determinant. -/
theorem trace_cube_traceless (A : Mat3 ℂ) (hA : Matrix.trace A = 0) :
    Matrix.trace (A * (A * A)) = 3 * Matrix.det A := by
  have hd : A 2 2 = -(A 0 0 + A 1 1) := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three] at hA
    linear_combination hA
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.det_fin_three, hd]
  ring

/-- Full cubic in the three matrix slots, specialized to the traceless space. -/
theorem traceless_traceCube_eq_three_norm (A B C : Mat3 ℂ) (hA : Matrix.trace A = 0) :
    let x := toTau (R := ℂ) (A, B, C)
    TauCeti.AlbertAlgebra.trace (x * (x * x)) =
      3 * (A.det + B.det + C.det - Matrix.trace (A * (B * C))) := by
  dsimp only
  rw [tauTrace_cube, trace_cube_traceless A hA, hA]
  ring

end ThirteenPlanes.Tits
