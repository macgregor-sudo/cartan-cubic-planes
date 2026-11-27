module

public import ThirteenPlanes.SignedTits

@[expose] public section

set_option backward.privateInPublic true

open scoped Matrix RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates AlbertLean.Generic.TitsLinear AlbertLean.Generic.TitsSquare

namespace ThirteenPlanes

noncomputable section

set_option maxHeartbeats 800000 in
private theorem compact_square_inner_eq_of_coordinates
    (y : Tits.CompactTitsTraceless) (A B : Mat3 ℂ)
    (hcoords : Tits.CompactTitsTraceless.coordinates y = (A, B, Bᴴ)) :
    ⟪Tits.CompactTits.square y.val, y.val⟫ =
      3 * (A.det.re + 2 * B.det.re - (Matrix.trace (A * (B * Bᴴ))).re) := by
  have hzero : Matrix.trace A = 0 := by
    simpa only [hcoords, Tits.trace3_eq_matrixTrace] using
      Tits.CompactTitsTraceless.complex_trace_zero y
  have h := Tits.tauTrace_compact_pairing (Tits.CompactTits.square y.val) y.val
  rw [Tits.CompactTits.coordinates_square, toTau_firstTitsSquare] at h
  have hcoords' : Tits.CompactTits.coordinates y.val = (A, B, Bᴴ) := hcoords
  rw [hcoords'] at h
  rw [mul_comm] at h
  have hc := Tits.traceless_traceCube_eq_three_norm A B Bᴴ hzero
  dsimp only at hc
  rw [hc, Matrix.det_conjTranspose] at h
  have hr := congrArg Complex.re h
  simp only [Complex.mul_re, show (3 : ℂ).re = 3 from Complex.natCast_re 3,
    show (3 : ℂ).im = 0 from Complex.natCast_im 3, zero_mul, sub_zero, Complex.add_re,
    Complex.sub_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re] at hr
  rw [← hr]
  ring

/-- The signed diagonal evaluation is three times the compact Tits cubic norm. -/
theorem signedEqualCubic_eq_realTitsNorm (x : SignedField) :
    let X := Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv x)
    signedEqualCubic.apply x x x =
      3 * (X.1.det.re + 2 * X.2.1.det.re -
        (Matrix.trace (X.1 * (X.2.1 * X.2.1ᴴ))).re) := by
  let y := gradedTitsEquiv x
  let X := Tits.CompactTitsTraceless.coordinates y
  have hX : Tits.CompactTitsTraceless.coordinates y = (X.1, X.2.1, X.2.1ᴴ) :=
    Prod.ext rfl (Prod.ext rfl (Tits.CompactTits.third_eq_adjoint y.val))
  dsimp only
  rw [signedEqualCubic_tits, compactTitsProduct_self]
  exact compact_square_inner_eq_of_coordinates y X.1 X.2.1 hX

end

end ThirteenPlanes
