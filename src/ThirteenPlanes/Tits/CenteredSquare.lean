module

public import TauCeti.Algebra.AlbertAlgebra.Determinant
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace ThirteenPlanes.Tits

open TauCeti TauCeti.AlbertAlgebra

/-- The trace norm of the fourth Jordan power at a traceless point. -/
theorem trace_square_square (x : AlbertAlgebra ℂ) (hx : trace x = 0) :
    trace ((x * x) * (x * x)) = (trace (x * x)) ^ 2 / 2 := by
  rw [trace_mul_assoc, mul_mul_self, mul_add, mul_sub]
  simp only [mul_smul_comm, mul_one, map_add, map_sub, map_smul, smul_eq_mul,
    hx, zero_mul, mul_zero, add_zero, zero_sub, spur_eq_invOf_two_mul, invOf_eq_inv]
  ring

/-- Centering the square removes precisely its component along the trace-three unit. -/
theorem centeredSquare_trace_norm (x : AlbertAlgebra ℂ) (hx : trace x = 0) :
    let q := x * x - (trace (x * x) / 3) • (1 : AlbertAlgebra ℂ)
    trace (q * q) = trace (x * x) ^ 2 / 6 := by
  dsimp only
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    map_sub, map_smul, smul_eq_mul, trace_one, trace_square_square x hx]
  ring

end ThirteenPlanes.Tits
