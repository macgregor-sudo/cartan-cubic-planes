module

public import ThirteenPlanes.Tits.RealForm
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators Matrix RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.Tits.CompactTits

noncomputable section

private abbrev MatrixIndex := Fin 3 × Fin 3
private abbrev EntryIndex := MatrixIndex ⊕ MatrixIndex
private abbrev Entries := EuclideanSpace ℂ EntryIndex

private def weightedEntries : CompactTits →ₗ[ℝ] (EntryIndex → ℂ) where
  toFun x := Sum.elim (fun ij => (coordinates x).1 ij.1 ij.2)
    (fun ij => Real.sqrt 2 • (coordinates x).2.1 ij.1 ij.2)
  map_add' x y := by
    funext i
    cases i <;> simp [map_add, smul_add]
  map_smul' r x := by
    funext i
    cases i <;> simp [map_smul, mul_left_comm]

private def embedding : CompactTits →ₗ[ℝ] Entries :=
  (WithLp.linearEquiv 2 ℝ (EntryIndex → ℂ)).symm.toLinearMap.comp weightedEntries

private theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  have hA : (coordinates x).1 = (coordinates y).1 := by
    funext i j
    exact congrArg (fun v : Entries => v (Sum.inl (i, j))) h
  have hB : (coordinates x).2.1 = (coordinates y).2.1 := by
    funext i j
    have hr : Real.sqrt 2 ≠ 0 := by positivity
    exact smul_right_injective ℂ hr (congrArg (fun v : Entries => v (Sum.inr (i, j))) h)
  apply CompactTits.ext
  exact Prod.ext hA (Prod.ext hB (by rw [third_eq_adjoint x, third_eq_adjoint y, hB]))

instance : NormedAddCommGroup CompactTits :=
  NormedAddCommGroup.induced _ _ embedding embedding_injective

instance : InnerProductSpace ℝ CompactTits :=
  InnerProductSpace.induced embedding

/-- The real first Tits trace form on the compact fixed locus. -/
def tracePairing (x y : CompactTits) : ℝ :=
  (Matrix.trace ((coordinates x).1 * (coordinates y).1)).re +
    2 * (Matrix.trace ((coordinates x).2.1 * (coordinates y).2.1ᴴ)).re

private theorem traceFrobenius_comm (X Y : Mat3 ℂ) :
    (Matrix.trace (Y * Xᴴ)).re = (Matrix.trace (X * Yᴴ)).re := by
  have h := Matrix.trace_conjTranspose (Y * Xᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
  simpa only [Complex.star_def, Complex.conj_re] using (congrArg Complex.re h).symm

private theorem sum_entry_pairing (X Y : Mat3 ℂ) :
    ∑ ij : MatrixIndex, (Y ij.1 ij.2 * star (X ij.1 ij.2)).re =
      (Matrix.trace (X * Yᴴ)).re := by
  rw [← traceFrobenius_comm X Y]
  simp [Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]

private theorem weighted_entry_pairing (a b : ℂ) :
    ((Real.sqrt 2 • b) * star (Real.sqrt 2 • a)).re = 2 * (b * star a).re := by
  rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, ← sq,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact Complex.reLm.map_smul (2 : ℝ) _

theorem inner_eq_tracePairing (x y : CompactTits) : ⟪x, y⟫ = tracePairing x y := by
  change ⟪embedding x, embedding y⟫ = _
  rw [PiLp.inner_apply]
  change (∑ q : EntryIndex, (weightedEntries y q * star (weightedEntries x q)).re) = _
  rw [Fintype.sum_sum_type]
  change (∑ ij : MatrixIndex,
      ((coordinates y).1 ij.1 ij.2 * star ((coordinates x).1 ij.1 ij.2)).re) +
    (∑ ij : MatrixIndex,
      ((Real.sqrt 2 • (coordinates y).2.1 ij.1 ij.2) *
        star (Real.sqrt 2 • (coordinates x).2.1 ij.1 ij.2)).re) = _
  simp only [weighted_entry_pairing, ← Finset.mul_sum, sum_entry_pairing, tracePairing,
    (hermitian y).eq]

theorem norm_sq_eq_tracePairing (x : CompactTits) : ‖x‖ ^ 2 = tracePairing x x := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_tracePairing]

theorem tracePairing_pos (x : CompactTits) (hx : x ≠ 0) : 0 < tracePairing x x := by
  rw [← norm_sq_eq_tracePairing]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)

/-- The metric is the restriction of the complex bilinear trace form. -/
theorem inner_eq_complexTrace_re (x y : CompactTits) :
    ⟪x, y⟫ = (trace3 ((coordinates x).1 * (coordinates y).1) +
      trace3 ((coordinates x).2.1 * (coordinates y).2.2) +
      trace3 ((coordinates x).2.2 * (coordinates y).2.1)).re := by
  simp only [inner_eq_tracePairing, tracePairing, trace3_eq_matrixTrace, third_eq_adjoint,
    Complex.add_re]
  rw [Matrix.trace_mul_comm (coordinates x).2.1ᴴ, traceFrobenius_comm]
  ring

theorem complexTrace_eq_inner (x y : CompactTits) :
    ((⟪x, y⟫ : ℝ) : ℂ) = trace3 ((coordinates x).1 * (coordinates y).1) +
      trace3 ((coordinates x).2.1 * (coordinates y).2.2) +
      trace3 ((coordinates x).2.2 * (coordinates y).2.1) := by
  have ha := Matrix.trace_conjTranspose ((coordinates x).1 * (coordinates y).1)
  rw [Matrix.conjTranspose_mul, (hermitian x).eq, (hermitian y).eq,
    Matrix.trace_mul_comm] at ha
  have hb := Matrix.trace_conjTranspose ((coordinates x).2.1 * (coordinates y).2.2)
  rw [Matrix.conjTranspose_mul, third_eq_adjoint y, Matrix.conjTranspose_conjTranspose,
    ← third_eq_adjoint x, Matrix.trace_mul_comm] at hb
  have hc := congrArg star hb
  rw [star_star] at hc
  let q : ℂ := trace3 ((coordinates x).1 * (coordinates y).1) +
    trace3 ((coordinates x).2.1 * (coordinates y).2.2) +
    trace3 ((coordinates x).2.2 * (coordinates y).2.1)
  have hq : star q = q := by
    simp only [q, trace3_eq_matrixTrace, star_add, third_eq_adjoint y]
    rw [← ha, ← hb, hc]
    ring
  change ((⟪x, y⟫ : ℝ) : ℂ) = q
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using inner_eq_complexTrace_re x y
  · have him := congrArg Complex.im hq
    simp only [Complex.star_def, Complex.conj_im] at him
    simpa only [Complex.ofReal_im] using (show 0 = q.im by linarith)

@[simp] theorem inner_one_right (x : CompactTits) : ⟪x, one⟫ = trace x := by
  simp [inner_eq_tracePairing, tracePairing, trace3_eq_matrixTrace, firstTitsOne]

theorem center_norm_sq (x : CompactTits) :
    ‖(center x).val‖ ^ 2 = ‖x‖ ^ 2 - (trace x) ^ 2 / 3 := by
  rw [← real_inner_self_eq_norm_sq]
  have hone : ‖one‖ ^ 2 = 3 := by
    rw [← real_inner_self_eq_norm_sq, inner_one_right, trace_one]
  have hleft : ⟪one, x⟫ = trace x := (real_inner_comm x one).trans (inner_one_right x)
  change ⟪x - (trace x / 3) • one, x - (trace x / 3) • one⟫ = _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_one_right, hleft, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hone]
  ring

theorem trace_square (x : CompactTits) : trace (square x) = ‖x‖ ^ 2 := by
  rw [trace_apply, coordinates_square, norm_sq_eq_tracePairing, tracePairing]
  simp only [firstTitsSquare, trace3_eq_matrixTrace, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, third_eq_adjoint,
    Complex.add_re, Complex.sub_re, smul_eq_mul]
  rw [mul_comm _ (3 : ℂ)]
  norm_num [Complex.mul_re]
  ring

end

end ThirteenPlanes.Tits.CompactTits
