module

public import ThirteenPlanes.Tits.CenteredSquare
public import ThirteenPlanes.Tits.Metric
public import ThirteenPlanes.Tits.TraceCubic

@[expose] public section

set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates AlbertLean.Generic.TitsLinear AlbertLean.Generic.TitsSquare

namespace ThirteenPlanes.Tits

noncomputable section

theorem tauTrace_compact_pairing (x y : CompactTits) :
    TauCeti.AlbertAlgebra.trace (toTau (CompactTits.coordinates x) * toTau (CompactTits.coordinates y)) =
      ((⟪x, y⟫ : ℝ) : ℂ) := by
  rw [CompactTits.complexTrace_eq_inner]
  simp only [trace3_eq_matrixTrace]
  exact tauTrace_toTau_mul_toTau _ _ _ _ _ _

namespace CompactTitsTraceless

/-- The trace-free Jordan square has squared kinetic norm `‖x‖⁴/6`. -/
theorem square_norm_sq (x : CompactTitsTraceless) : ‖square x‖ ^ 2 = ‖x‖ ^ 4 / 6 := by
  let a := toTau (coordinates x)
  have hzero : TauCeti.AlbertAlgebra.trace a = 0 := by
    change TauCeti.AlbertAlgebra.trace (toTau (coordinates x)) = 0
    rw [tauTrace_toTau, ← trace3_eq_matrixTrace, complex_trace_zero]
  have hs : toTau (CompactTits.coordinates (CompactTits.square x.val)) = a * a := by
    rw [CompactTits.coordinates_square, toTau_firstTitsSquare]
    rfl
  have hnorm₀ : TauCeti.AlbertAlgebra.trace (a * a) = ((‖x.val‖ ^ 2 : ℝ) : ℂ) := by
    change TauCeti.AlbertAlgebra.trace
      (toTau (CompactTits.coordinates x.val) * toTau (CompactTits.coordinates x.val)) = _
    rw [tauTrace_compact_pairing, real_inner_self_eq_norm_sq]
  have hnorm₁ : TauCeti.AlbertAlgebra.trace ((a * a) * (a * a)) =
      ((‖CompactTits.square x.val‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hs, tauTrace_compact_pairing, real_inner_self_eq_norm_sq]
  have h := trace_square_square a hzero
  rw [hnorm₀, hnorm₁] at h
  have hfull : ‖CompactTits.square x.val‖ ^ 2 = ‖x.val‖ ^ 4 / 2 := by
    have hc : ((‖CompactTits.square x.val‖ ^ 2 : ℝ) : ℂ) =
        ((‖x.val‖ ^ 4 / 2 : ℝ) : ℂ) := by
      rw [h]
      push_cast
      ring
    exact_mod_cast hc
  change ‖(CompactTits.center (CompactTits.square x.val)).val‖ ^ 2 = ‖x.val‖ ^ 4 / 6
  rw [CompactTits.center_norm_sq, hfull, CompactTits.trace_square]
  ring

end CompactTitsTraceless

end

end ThirteenPlanes.Tits
