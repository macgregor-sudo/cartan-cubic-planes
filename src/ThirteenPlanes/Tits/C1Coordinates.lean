/- SPDX-License-Identifier: Apache-2.0
Ported from AlbertLean/Generic/C1Coordinates.lean at dd06ef5d423a0e4a5d814d2c221e999b98887ee1. Module imports adapted for Lean 4.36. -/
module

public import TauCeti.Algebra.AlbertAlgebra.Basic

@[expose] public section

/-!
Explicit first-Tits coordinates and their map to the Tau model.
The matrix-triple carrier has an inherited componentwise product and unit.
The intended operations are the explicitly named square, sharp, unit and
polarized product below; no new ring instance is installed on this carrier.
-/

noncomputable section
namespace AlbertLean.Generic.C1Coordinates

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R
abbrev FirstTits (R : Type*) := Mat3 R × Mat3 R × Mat3 R
abbrev Albert (R : Type*) := TauCeti.AlbertAlgebra R

variable {R : Type*}

def toTauRaw [Neg R] (z : FirstTits R) : Albert R :=
  ⟨![z.1 0 0, z.1 1 1, z.1 2 2],
    ![⟨z.1 1 2, z.1 2 1, ![z.2.2 0 0, z.2.2 1 0, z.2.2 2 0], ![-(z.2.1 0 0), -(z.2.1 0 1), -(z.2.1 0 2)]⟩, ⟨z.1 2 0, z.1 0 2, ![z.2.2 0 1, z.2.2 1 1, z.2.2 2 1], ![-(z.2.1 1 0), -(z.2.1 1 1), -(z.2.1 1 2)]⟩, ⟨z.1 0 1, z.1 1 0, ![z.2.2 0 2, z.2.2 1 2, z.2.2 2 2], ![-(z.2.1 2 0), -(z.2.1 2 1), -(z.2.1 2 2)]⟩]⟩

def fromTauRaw [Neg R] (x : Albert R) : FirstTits R :=
  (![![x.diag 0, (x.offDiag 2).a, (x.offDiag 1).b], ![(x.offDiag 2).b, x.diag 1, (x.offDiag 0).a], ![(x.offDiag 1).a, (x.offDiag 0).b, x.diag 2]],
   ![![-((x.offDiag 0).w 0), -((x.offDiag 0).w 1), -((x.offDiag 0).w 2)], ![-((x.offDiag 1).w 0), -((x.offDiag 1).w 1), -((x.offDiag 1).w 2)], ![-((x.offDiag 2).w 0), -((x.offDiag 2).w 1), -((x.offDiag 2).w 2)]],
   ![![(x.offDiag 0).v 0, (x.offDiag 1).v 0, (x.offDiag 2).v 0], ![(x.offDiag 0).v 1, (x.offDiag 1).v 1, (x.offDiag 2).v 1], ![(x.offDiag 0).v 2, (x.offDiag 1).v 2, (x.offDiag 2).v 2]])

def firstTitsOne [Zero R] [One R] : FirstTits R := (1, 0, 0)

def trace3 [Add R] (A : Mat3 R) : R := A 0 0 + A 1 1 + A 2 2

def adjugate3 [CommRing R] (A : Mat3 R) : Mat3 R :=
  ![![A 1 1 * A 2 2 - A 1 2 * A 2 1, A 0 2 * A 2 1 - A 0 1 * A 2 2, A 0 1 * A 1 2 - A 0 2 * A 1 1], ![A 1 2 * A 2 0 - A 1 0 * A 2 2, A 0 0 * A 2 2 - A 0 2 * A 2 0, A 0 2 * A 1 0 - A 0 0 * A 1 2], ![A 1 0 * A 2 1 - A 1 1 * A 2 0, A 0 1 * A 2 0 - A 0 0 * A 2 1, A 0 0 * A 1 1 - A 0 1 * A 1 0]]

def firstTitsSharp [CommRing R] (z : FirstTits R) : FirstTits R :=
  (adjugate3 z.1 - z.2.1 * z.2.2,
   adjugate3 z.2.2 - z.1 * z.2.1,
   adjugate3 z.2.1 - z.2.2 * z.1)

def firstTitsSquare [CommRing R] (z : FirstTits R) : FirstTits R :=
  (z.1 * z.1 - z.2.1 * z.2.2 + trace3 (z.2.1 * z.2.2) • (1 : Mat3 R),
   adjugate3 z.2.2 - z.1 * z.2.1 + trace3 z.1 • z.2.1,
   adjugate3 z.2.1 - z.2.2 * z.1 + trace3 z.1 • z.2.2)

def polarProduct [CommRing R] [Invertible (2 : R)]
    (square : FirstTits R → FirstTits R) (x y : FirstTits R) : FirstTits R :=
  ⅟(2 : R) • (square (x + y) - square x - square y)

end AlbertLean.Generic.C1Coordinates
