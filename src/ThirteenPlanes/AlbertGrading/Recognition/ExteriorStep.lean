module

public import ThirteenPlanes.AlbertGrading.Recognition.Systems

@[expose] public section

/-!
# A frame unbiased to the four eigenframes is orthogonal to `Q₀⁰`

The step "`U_H ⊥ Q₀⁰`" of the proof of the recognition of systems with 52 positive shares, obtained here from unbiasedness of `H`
with the four eigenframes of the `ι₀(D_v)` (planes spanning `Q₀⁰`), and facts on graded frames.
-/

open scoped Matrix BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem gradedFrame_contrast (g : Charge) : titsContrast (gradedFrame g) = titsBasis g := by
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  simp only [titsContrast, gradedFrame_coordinates, gradedCoords, sum_zmod3, neg_zero,
    chargePhase_zero, chargePhase_one', chargePhase_two',
    show chargePhase (-(1 : ZMod 3)) = chargeRoot ^ 2 from rfl,
    show chargePhase (-(2 : ZMod 3)) = chargeRoot from pow_one _]
  match_scalars <;>
    first
    | linear_combination (1 / 3 : ℂ) * hq
    | linear_combination (2 / 3 : ℂ) * hc
    | linear_combination (1 / 3 : ℂ) * hq + (1 / 3 : ℂ) * chargeRoot * hc
    | ring

theorem charge_ne_neg {g : Charge} (hg : g ≠ 0) : g ≠ -g := by
  intro e
  apply hg
  have h := charge_add_self g
  rw [← e] at h
  exact add_eq_left.mp h

theorem gradedRange_eq_imp {g g' : Charge} (hg : g ≠ 0)
    (h : Set.range (gradedFrame g) = Set.range (gradedFrame g')) : g' = g ∨ g' = -g := by
  obtain ⟨b, hb⟩ : gradedFrame g 0 ∈ Set.range (gradedFrame g') := h ▸ Set.mem_range_self 0
  have hc := congrArg (fun x => coef g (CompactTits.coordinates x)) hb
  simp only [gradedFrame_coordinates, gradedCoords, map_smul, map_add, coef_one, coef_titsBasis,
    if_neg hg, neg_zero, chargePhase_zero, if_pos rfl, if_neg (charge_ne_neg hg),
    smul_eq_mul] at hc
  by_contra hne
  push_neg at hne
  have h1 : g ≠ g' := fun e => hne.1 e.symm
  have h2 : g ≠ -g' := fun e => hne.2 (by rw [e, neg_neg])
  rw [if_neg h1, if_neg h2] at hc
  norm_num at hc

theorem eigen_hidden_zero (v : WeylLabel) (b : ZMod 3) :
    (CompactTits.coordinates (gradedFrame (chargeFrom v 0) b)).2.1 = 0 := by
  simp only [gradedFrame_coordinates, gradedCoords, titsBasis, iota, Pi.neg_apply,
    chargeFrom_third, neg_zero, firstTitsOne, show (0 : ZMod 3) ≠ 1 by decide, if_false,
    Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
  simp

/-- A frame `p` unbiased to the eigenframes of all `ι₀(D_v)` has plane orthogonal to `Q₀⁰`. -/
theorem exterior_orthogonal {p : ZMod 3 → CompactTits} (hp : IsTitsFrame p)
    (h : ∀ v : WeylLabel, v ≠ 0 → ∀ a b,
      CompactTits.trace (CompactTits.product (p a) (gradedFrame (chargeFrom v 0) b)) = 1 / 3) :
    (titsFramePlane p).IsOrtho visibleTraceless := by
  -- the visible block of each `p a` is `1/3`
  have hA : ∀ a, (CompactTits.coordinates (p a)).1 = (1 / 3 : ℂ) • (1 : Mat3 ℂ) := by
    intro a
    have hcoef : ∀ v : WeylLabel, v ≠ 0 → coef (chargeFrom v 0) (CompactTits.coordinates (p a)) = 0 := by
      intro v hv
      have hT : titsTraceForm (CompactTits.coordinates (p a)) (titsBasis (chargeFrom (-v) 0)) = 0 := by
        rw [← gradedFrame_contrast, titsContrast, ← traceBilin_apply, map_sum]
        simp only [map_smul, traceBilin_apply, ← complex_trace_product,
          h (-v) (neg_ne_zero.mpr hv), smul_eq_mul]
        rw [← Finset.sum_mul, chargePhase_sum, zero_mul]
      rw [traceForm_titsBasis_right, ← chargeFrom_neg, neg_neg, neg_zero] at hT
      linear_combination hT / 3
    rw [first_of_coef _ hcoef]
    congr 1
    have h1 : tr1 (CompactTits.coordinates (p a)) = 1 := by
      rw [tr1_apply, ← CompactTits.complex_trace_eq, hp.2.1 a]; simp
    have h2 : tr1 (CompactTits.coordinates (p a)) = 3 * coef 0 (CompactTits.coordinates (p a)) := by
      rw [tr1_apply, first_of_coef _ hcoef]; simp [trace3]; ring
    linear_combination (h1 - h2) / 3
  rw [Submodule.IsOrtho, titsFramePlane, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal]
  rintro x ⟨hx1, -⟩
  rw [CompactTits.inner_eq_tracePairing, CompactTits.tracePairing]
  have hy : (CompactTits.coordinates (p a - (1 / 3 : ℝ) • CompactTits.one)).1 = 0 := by
    simp only [map_sub, map_smul, CompactTits.coordinates_one, firstTitsOne, Prod.fst_sub,
      Prod.smul_fst, hA a]
    rw [← Complex.coe_smul]; push_cast; exact sub_self _
  rw [hy, hx1]
  simp

end

end ThirteenPlanes.AlbertGrading
