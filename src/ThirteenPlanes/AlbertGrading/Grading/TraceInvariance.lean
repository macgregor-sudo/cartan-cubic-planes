module

public import ThirteenPlanes.Graded.Characters
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

set_option backward.privateInPublic true

/-! # Jordan automorphisms preserve the trace

For a product-preserving real-linear bijection `φ` of the compact Albert algebra,
`L_{φ x} = φ L_x φ⁻¹`, so `x ↦ Tr L_x` is invariant. Averaging over the accepted
reference grading action shows `Tr L_x = 9 tr x`, hence `tr (φ x) = tr x`. -/

namespace ThirteenPlanes.AlbertGrading.Grading

open Glennie ThirteenPlanes.Graded

noncomputable section

/-- `x ↦ Tr(L_x)` on the compact Albert algebra. -/
def multTrace : Glennie.Albert →ₗ[ℝ] ℝ := (LinearMap.trace ℝ Glennie.Albert).comp jordanLinear

theorem multTrace_aut (φ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hφ : ∀ x y, φ (jordan x y) = jordan (φ x) (φ y)) (x : Glennie.Albert) :
    multTrace (φ x) = multTrace x := by
  have h : jordanLinear (φ x) = φ.conj (jordanLinear x) := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, jordanLinear_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, jordanLinear_apply, hφ, LinearEquiv.apply_symm_apply]
  simp only [multTrace, LinearMap.comp_apply, h, LinearMap.trace_conj']

private theorem dot_add_left' (x y z : Charge) :
    chargeDot (x + y) z = chargeDot x z + chargeDot y z := by
  simp [chargeDot, add_mul, Finset.sum_add_distrib]

/-- Orthogonality of the ternary characters. -/
theorem sum_chargePhase_dot (q : Charge) :
    (∑ s : Charge, chargePhase (chargeDot s q)) = if q = 0 then 27 else 0 := by
  split_ifs with hq
  · subst hq
    simp [chargeDot]
  · obtain ⟨j, hj⟩ : ∃ j, q j ≠ 0 := by
      by_contra h
      push Not at h
      exact hq (funext h)
    let e : Charge := Pi.single j 1
    have hej : chargeDot e q = q j := by
      unfold chargeDot
      rw [Finset.sum_eq_single j]
      · simp [e]
      · intro i _ hi; simp [e, Pi.single_eq_of_ne hi]
      · simp
    have h0 : (∑ s : Charge, chargePhase (chargeDot (s + e) q)) =
        ∑ s : Charge, chargePhase (chargeDot s q) :=
      Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
    have h1 : (∑ s : Charge, chargePhase (chargeDot (s + e) q)) =
        chargePhase (q j) * ∑ s : Charge, chargePhase (chargeDot s q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [dot_add_left', chargePhase_add, hej, mul_comm]
    have hshift : (∑ s : Charge, chargePhase (chargeDot s q)) =
        chargePhase (q j) * ∑ s : Charge, chargePhase (chargeDot s q) := h0.symm.trans h1
    have hne : chargePhase (q j) ≠ 1 := by
      intro h
      apply hj
      apply FiniteGroup.chargePhase_injective
      rw [h, chargePhase_zero]
    have h1 : (1 - chargePhase (q j)) * ∑ s : Charge, chargePhase (chargeDot s q) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h

private theorem coords_trace (x : Glennie.Albert) :
    Glennie.trace x = 3 * ((nativeSignedCoordinates x).val 0).re := by
  have hk : signedUnitalEquiv (nativeSignedCoordinates x) = nativeCompactTitsEquiv x := by
    show signedUnitalEquiv
      ((signedUnitalEquiv.trans nativeCompactTitsEquiv.symm.toLinearEquiv).symm x) = _
    rw [LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [← nativeCompactTitsEquiv_trace, ← hk, signedUnitalEquiv_trace]

/-- Averaging over the reference grading projects onto the unit line. -/
theorem sum_nativeCharacterAction (x : Glennie.Albert) :
    (∑ s : Charge, nativeCharacterAction s x) = (9 * Glennie.trace x) • (1 : Glennie.Albert) := by
  apply nativeSignedCoordinates.injective
  apply Subtype.ext
  funext q
  rw [map_sum, map_smul, nativeSignedCoordinates_one, Submodule.coe_sum, Finset.sum_apply]
  simp only [nativeCharacterAction_coordinates, characterAction_apply]
  rw [← Finset.sum_mul, sum_chargePhase_dot]
  change _ = ((9 * Glennie.trace x : ℝ) : ℂ) * chargeBasisVector 0 q
  have hreal : (nativeSignedCoordinates x).val 0 =
      (((nativeSignedCoordinates x).val 0).re : ℂ) := by
    have h := (nativeSignedCoordinates x).property 0
    rw [neg_zero] at h
    apply Complex.ext
    · simp
    · have := congrArg Complex.im h
      simp only [Complex.star_def, Complex.conj_im] at this
      simp only [Complex.ofReal_im]
      linarith
  by_cases hq : q = 0
  · subst hq
    rw [ite_eq_left rfl, coords_trace, hreal]
    simp [chargeBasisVector]
    push_cast
    ring
  · rw [ite_eq_right hq, zero_mul]
    simp [chargeBasisVector, hq]

private theorem multTrace_one : multTrace (1 : Glennie.Albert) = 27 := by
  have h : jordanLinear (1 : Glennie.Albert) = LinearMap.id := by
    apply LinearMap.ext; intro y; simp
  simp only [multTrace, LinearMap.comp_apply, h, LinearMap.trace_id, Glennie.albert_finrank]
  norm_num

/-- `Tr L_x = 9 tr x` on the compact Albert algebra. -/
theorem multTrace_eq (x : Glennie.Albert) : multTrace x = 9 * Glennie.trace x := by
  have hinv (s : Charge) : multTrace (nativeCharacterAction s x) = multTrace x :=
    multTrace_aut (nativeCharacterAction s) (nativeCharacterAction_product s) x
  have h := congrArg multTrace (sum_nativeCharacterAction x)
  rw [map_sum, map_smul, multTrace_one, smul_eq_mul] at h
  simp only [hinv, Finset.sum_const, Finset.card_univ] at h
  have hc : Fintype.card Charge = 27 := by simp [Charge]
  rw [hc] at h
  simp only [nsmul_eq_mul] at h
  push_cast at h
  linarith

/-- Every product-preserving real-linear bijection of the compact Albert algebra
preserves the trace. -/
/- Trace preservation is the conclusion of Yokota, Exceptional Lie Groups
(arXiv:0902.0431), Lemma 2.2.1(2). This proof recovers the Jordan trace from the
trace of left multiplication using the ternary grading. -/
theorem trace_aut (φ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hφ : ∀ x y, φ (jordan x y) = jordan (φ x) (φ y)) (x : Glennie.Albert) :
    Glennie.trace (φ x) = Glennie.trace x := by
  have h := multTrace_aut φ hφ x
  rw [multTrace_eq, multTrace_eq] at h
  linarith

/-- Such a bijection fixes the unit. -/
theorem one_aut (φ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hφ : ∀ x y, φ (jordan x y) = jordan (φ x) (φ y)) : φ 1 = 1 := by
  have h := hφ 1 (φ.symm 1)
  rw [jordan_unit_left, LinearEquiv.apply_symm_apply, jordan_unit_right] at h
  exact h.symm

/-- Such a bijection preserves the trace form. -/
theorem inner_aut (φ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hφ : ∀ x y, φ (jordan x y) = jordan (φ x) (φ y)) (x y : Glennie.Albert) :
    Glennie.inner (φ x) (φ y) = Glennie.inner x y := by
  unfold Glennie.inner
  rw [← hφ, trace_aut φ hφ]

end

end ThirteenPlanes.AlbertGrading.Grading
