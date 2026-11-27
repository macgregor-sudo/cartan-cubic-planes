module

public import ThirteenPlanes.Tits.TitsSquare
public import TauCeti.Algebra.AlbertAlgebra.Determinant
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace ThirteenPlanes

open AlbertLean.Generic.C1Coordinates AlbertLean.Generic.TitsLinear AlbertLean.Generic.TitsSquare
open TauCeti.AlbertAlgebra

/-- The complex first Tits construction in matrix coordinates satisfies the cubic
characteristic identity for its named unit and Jordan product. -/
theorem titsCubicIdentity (x : FirstTits ℂ) :
    polarProduct firstTitsSquare x (firstTitsSquare x) =
      trace3 x.1 • firstTitsSquare x - spur (toTau x) • x +
      det (toTau x) • firstTitsOne := by
  apply toTau.injective
  rw [toTau_polarProduct, toTau_firstTitsSquare, map_add, map_sub, map_smul,
    map_smul, map_smul, toTau_firstTitsSquare, toTau_firstTitsOne,
    TauCeti.AlbertAlgebra.mul_mul_self, tauTrace_toTau, trace3_eq_matrixTrace]

end ThirteenPlanes
