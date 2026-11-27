module

public import ThirteenPlanes.AlbertGrading.Grading.PhasesMain

@[expose] public section

/-! # complex phases of graded plane coefficients, final step -/

namespace ThirteenPlanes.AlbertGrading

open Grading Grading.JC

noncomputable section

namespace Grading

variable {ρ : TernaryAction}

/-- The three-plane term in coordinates `w_i`. -/
theorem cubic_three (hρ : IsTernaryGrading ρ) {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0)
    (h₁ : g + h ≠ 0) {B₁ B₂ B₃ : JC} (m₁ : B₁ ∈ charSpace ρ g) (m₂ : B₂ ∈ charSpace ρ h)
    (m₃ : B₃ ∈ charSpace ρ (g + h)) {K : ℂ} (hK : mul B₁ B₂ = K • B₃)
    (h3 : ip B₃ (conj B₃) = 2) (w₁ w₂ w₃ : ℂ) :
    (ip (mul ((1 / 2 : ℂ) • (w₁ • B₁ + star w₁ • conj B₁))
        ((1 / 2 : ℂ) • (w₂ • B₂ + star w₂ • conj B₂)))
      ((1 / 2 : ℂ) • (w₃ • B₃ + star w₃ • conj B₃))).re = (1 / 2) * (K * w₁ * w₂ * star w₃).re := by
  have c₁ := conj_mem_charSpace m₁
  have c₂ := conj_mem_charSpace m₂
  have c₃ := conj_mem_charSpace m₃
  have z1 : ip (mul B₁ B₂) B₃ = 0 := ip_eq_zero_of_charSpace hρ (mul_mem_charSpace hρ m₁ m₂) m₃
    (charge_add_self_ne_zero h₁)
  have z2 : ip (mul B₁ (conj B₂)) B₃ = 0 := ip_eq_zero_of_charSpace hρ (mul_mem_charSpace hρ m₁ c₂) m₃
    (by rw [show g + -h + (g + h) = g + g by abel]; exact charge_add_self_ne_zero hg)
  have z3 : ip (mul B₁ (conj B₂)) (conj B₃) = 0 :=
    ip_eq_zero_of_charSpace hρ (mul_mem_charSpace hρ m₁ c₂) c₃
      (by rw [show g + -h + -(g + h) = -(h + h) by abel]
          exact neg_ne_zero.mpr (charge_add_self_ne_zero hh))
  have z4 : ip (mul (conj B₁) B₂) B₃ = 0 := ip_eq_zero_of_charSpace hρ (mul_mem_charSpace hρ c₁ m₂) m₃
    (by rw [show -g + h + (g + h) = h + h by abel]; exact charge_add_self_ne_zero hh)
  have z5 : ip (mul (conj B₁) B₂) (conj B₃) = 0 :=
    ip_eq_zero_of_charSpace hρ (mul_mem_charSpace hρ c₁ m₂) c₃
      (by rw [show -g + h + -(g + h) = -(g + g) by abel]
          exact neg_ne_zero.mpr (charge_add_self_ne_zero hg))
  have z6 : ip (mul (conj B₁) (conj B₂)) (conj B₃) = 0 :=
    ip_eq_zero_of_charSpace hρ (mul_mem_charSpace hρ c₁ c₂) c₃
      (by rw [show -g + -h + -(g + h) = -((g + h) + (g + h)) by abel]
          exact neg_ne_zero.mpr (charge_add_self_ne_zero h₁))
  have n1 : ip (mul B₁ B₂) (conj B₃) = K * 2 := by rw [hK, ip_smul_left, h3]
  have n2 : ip (mul (conj B₁) (conj B₂)) B₃ = star K * 2 := by
    rw [← conj_mul, hK, conj_smul, ip_smul_left, ip_comm, h3]
  have key : ip (mul ((1 / 2 : ℂ) • (w₁ • B₁ + star w₁ • conj B₁))
        ((1 / 2 : ℂ) • (w₂ • B₂ + star w₂ • conj B₂)))
      ((1 / 2 : ℂ) • (w₃ • B₃ + star w₃ • conj B₃)) =
      (1 / 4) * (K * w₁ * w₂ * star w₃) + (1 / 4) * star (K * w₁ * w₂ * star w₃) := by
    simp only [mul_add_left, mul_add_right, mul_smul_left, mul_smul_right, ip_add_left,
      ip_add_right, ip_smul_left, ip_smul_right, z1, z2, z3, z4, z5, z6, n1, n2]
    rw [star_mul', star_mul', star_mul', star_star]
    ring
  rw [key]
  simp [Complex.add_re, Complex.mul_re]
  ring

theorem pointOf_ne {k k' : Charge} (hk : k ≠ 0) (hk' : k' ≠ 0) (h₁ : k + k' ≠ 0) (h₂ : k - k' ≠ 0) :
    pointOf hk ≠ pointOf hk' := by
  intro h
  have a := pointOf_rep hk
  have b := pointOf_rep hk'
  rw [h] at a
  rcases a with a | a <;> rcases b with b | b
  · exact h₂ (sub_eq_zero.mpr (a.symm.trans b))
  · exact h₁ (by rw [← a, b, neg_add_cancel])
  · exact h₁ (by rw [← neg_neg k, ← a, b, neg_add_cancel])
  · exact h₂ (by rw [← neg_neg k, ← a, b, neg_neg, sub_self])

section

variable (hρ : IsTernaryGrading ρ) (ψ : SignedPlaneIndex → (ℂ →ₗ[ℝ] NativeTraceless))
  (hψP : ∀ p ζ, ψ p ζ ∈ pointPlane ρ p)
  (hnorm : ∀ ζ : SignedPlaneIndex → ℂ, ‖∑ p, ψ p (ζ p)‖ ^ 2 = ∑ p, ‖ζ p‖ ^ 2)
  (hreal : ∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r → ∀ ζ₁ ζ₂ ζ₃ : ℂ,
    nativeEqualCubic.apply (ψ p (star ζ₁)) (ψ q (star ζ₂)) (ψ r (star ζ₃)) =
      nativeEqualCubic.apply (ψ p ζ₁) (ψ q ζ₂) (ψ r ζ₃))
include hρ hψP hnorm hreal

/-- Real three-plane coefficients force real structure constants. -/
theorem basis_constant_real {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0) (h₁ : g + h ≠ 0)
    (h₂ : g - h ≠ 0) {K : ℂ}
    (hK : mul (basisElt (ρ := ρ) ψ g) (basisElt (ρ := ρ) ψ h) = K • basisElt (ρ := ρ) ψ (g + h)) :
    K.im = 0 := by
  obtain ⟨σ₁, hs₁, h1₁, ⟨ζ₀, hζ₀⟩, f₁⟩ := of_psi_basis hρ ψ hψP hnorm hg
  obtain ⟨σ₂, hs₂, h1₂, -, f₂⟩ := of_psi_basis hρ ψ hψP hnorm hh
  obtain ⟨σ₃, hs₃, h1₃, -, f₃⟩ := of_psi_basis hρ ψ hψP hnorm h₁
  have d12 : pointOf hg ≠ pointOf hh := pointOf_ne hg hh h₁ h₂
  have d13 : pointOf hg ≠ pointOf h₁ := pointOf_ne hg h₁
    (by rw [← add_assoc, charge_add_self, ← sub_eq_neg_add, ← neg_sub]; exact neg_ne_zero.mpr h₂)
    (by rw [sub_add_cancel_left]; exact neg_ne_zero.mpr hh)
  have d23 : pointOf hh ≠ pointOf h₁ := pointOf_ne hh h₁
    (by rw [show h + (g + h) = g - h by rw [add_comm g h, ← add_assoc, charge_add_self]; abel]
        exact h₂)
    (by rw [show h - (g + h) = -g by abel]; exact neg_ne_zero.mpr hg)
  have e := hreal _ _ _ d12 d13 d23 ζ₀ 1 1
  rw [apply_eq_ip, apply_eq_ip, f₁, f₂, f₃, f₁, f₂, f₃] at e
  have m₁ := basisElt_mem hρ ψ hψP hnorm hg
  have m₂ := basisElt_mem hρ ψ hψP hnorm hh
  have m₃ := basisElt_mem hρ ψ hψP hnorm h₁
  have i₃ := basisElt_ip hρ ψ hψP hnorm h₁
  rw [cubic_three hρ hg hh h₁ m₁ m₂ m₃ hK i₃, cubic_three hρ hg hh h₁ m₁ m₂ m₃ hK i₃] at e
  simp only [hs₁, hs₂, hs₃, star_one, h1₂, h1₃, hζ₀] at e
  simp [Complex.mul_re] at e
  linarith

/-- Complex phases of graded plane coefficients, the contradiction. -/
theorem no_real_coordinates : False := by
  let g₁ : Charge := ![1, 0, 0]
  let g₂ : Charge := ![0, 1, 0]
  let g₃ : Charge := ![0, 0, 1]
  let g₄ : Charge := ![2, 2, 2]
  have n₁ : g₁ ≠ 0 := by decide
  have n₂ : g₂ ≠ 0 := by decide
  have n₃ : g₃ ≠ 0 := by decide
  have n₄ : g₄ ≠ 0 := by decide
  -- the structure constants of the six pairs
  obtain ⟨K₁₂, e₁₂, k₁₂⟩ := basis_constant hρ ψ hψP hnorm n₁ n₂ (by decide) (by decide)
  obtain ⟨K₃₄, e₃₄, k₃₄⟩ := basis_constant hρ ψ hψP hnorm n₃ n₄ (by decide) (by decide)
  obtain ⟨K₁₃, e₁₃, k₁₃⟩ := basis_constant hρ ψ hψP hnorm n₁ n₃ (by decide) (by decide)
  obtain ⟨K₂₄, e₂₄, k₂₄⟩ := basis_constant hρ ψ hψP hnorm n₂ n₄ (by decide) (by decide)
  obtain ⟨K₁₄, e₁₄, k₁₄⟩ := basis_constant hρ ψ hψP hnorm n₁ n₄ (by decide) (by decide)
  obtain ⟨K₂₃, e₂₃, k₂₃⟩ := basis_constant hρ ψ hψP hnorm n₂ n₃ (by decide) (by decide)
  have r₁₂ := basis_constant_real hρ ψ hψP hnorm hreal n₁ n₂ (by decide) (by decide) e₁₂
  have r₃₄ := basis_constant_real hρ ψ hψP hnorm hreal n₃ n₄ (by decide) (by decide) e₃₄
  have r₁₃ := basis_constant_real hρ ψ hψP hnorm hreal n₁ n₃ (by decide) (by decide) e₁₃
  have r₂₄ := basis_constant_real hρ ψ hψP hnorm hreal n₂ n₄ (by decide) (by decide) e₂₄
  have r₁₄ := basis_constant_real hρ ψ hψP hnorm hreal n₁ n₄ (by decide) (by decide) e₁₄
  have r₂₃ := basis_constant_real hρ ψ hψP hnorm hreal n₂ n₃ (by decide) (by decide) e₂₃
  -- opposite sums give conjugate basis elements
  have o₁ : basisElt (ρ := ρ) ψ (g₃ + g₄) = conj (basisElt (ρ := ρ) ψ (g₁ + g₂)) := by
    rw [show g₃ + g₄ = -(g₁ + g₂) by decide]; exact basisElt_neg hρ ψ hψP hnorm (by decide)
  have o₂ : basisElt (ρ := ρ) ψ (g₂ + g₄) = conj (basisElt (ρ := ρ) ψ (g₁ + g₃)) := by
    rw [show g₂ + g₄ = -(g₁ + g₃) by decide]; exact basisElt_neg hρ ψ hψP hnorm (by decide)
  have o₃ : basisElt (ρ := ρ) ψ (g₂ + g₃) = conj (basisElt (ρ := ρ) ψ (g₁ + g₄)) := by
    rw [show g₂ + g₃ = -(g₁ + g₄) by decide]; exact basisElt_neg hρ ψ hψP hnorm (by decide)
  have i₁ := basisElt_ip hρ ψ hψP hnorm (show g₁ + g₂ ≠ 0 by decide)
  have i₂ := basisElt_ip hρ ψ hψP hnorm (show g₁ + g₃ ≠ 0 by decide)
  have i₃ := basisElt_ip hρ ψ hψP hnorm (show g₁ + g₄ ≠ 0 by decide)
  have m₁ := basisElt_mem hρ ψ hψP hnorm n₁
  have m₂ := basisElt_mem hρ ψ hψP hnorm n₂
  have m₃ := basisElt_mem hρ ψ hψP hnorm n₃
  have m₄ := basisElt_mem hρ ψ hψP hnorm n₄
  have q := quartic_eq_zero _ _ _ _ (tr_eq_zero_of_mem hρ n₁ m₁) (tr_eq_zero_of_mem hρ n₂ m₂)
    (tr_eq_zero_of_mem hρ n₃ m₃) (tr_eq_zero_of_mem hρ n₄ m₄)
  have z (a b : Charge) (hab : a + b ≠ 0) {x y : JC} (hx : x ∈ charSpace ρ a)
      (hy : y ∈ charSpace ρ b) : ip x y = 0 := ip_eq_zero_of_charSpace hρ hx hy hab
  unfold quartic at q
  rw [e₁₂, e₃₄, e₁₃, e₂₄, e₁₄, e₂₃, o₁, o₂, o₃, ip_smul_left, ip_smul_right, ip_smul_left,
    ip_smul_right, ip_smul_left, ip_smul_right, i₁, i₂, i₃,
    z g₁ g₂ (by decide) m₁ m₂, z g₃ g₄ (by decide) m₃ m₄, z g₁ g₃ (by decide) m₁ m₃,
    z g₂ g₄ (by decide) m₂ m₄, z g₁ g₄ (by decide) m₁ m₄, z g₂ g₃ (by decide) m₂ m₃] at q
  -- real form
  have re_of (K : ℂ) (hK : K.im = 0) (hKK : K * star K = 1 / 6) : K.re * K.re = 1 / 6 := by
    have := congrArg Complex.re hKK
    simp [Complex.mul_re, hK] at this
    linarith
  have a₁ := re_of _ r₁₂ k₁₂
  have a₂ := re_of _ r₃₄ k₃₄
  have a₃ := re_of _ r₁₃ k₁₃
  have a₄ := re_of _ r₂₄ k₂₄
  have a₅ := re_of _ r₁₄ k₁₄
  have a₆ := re_of _ r₂₃ k₂₃
  have qr := congrArg Complex.re q
  simp [Complex.mul_re, r₁₂, r₃₄, r₁₃, r₂₄, r₁₄, r₂₃] at qr
  set x := K₁₂.re * K₃₄.re
  set y := K₁₃.re * K₂₄.re
  set w := K₁₄.re * K₂₃.re
  have sum : x + y + w = 0 := by linarith
  have sx : (x - 1 / 6) * (x + 1 / 6) = 0 := by
    have : x * x = 1 / 36 := by
      simp only [x]
      calc K₁₂.re * K₃₄.re * (K₁₂.re * K₃₄.re) = (K₁₂.re * K₁₂.re) * (K₃₄.re * K₃₄.re) := by ring
        _ = 1 / 36 := by rw [a₁, a₂]; norm_num
    linear_combination this
  have sy : (y - 1 / 6) * (y + 1 / 6) = 0 := by
    have : y * y = 1 / 36 := by
      simp only [y]
      calc K₁₃.re * K₂₄.re * (K₁₃.re * K₂₄.re) = (K₁₃.re * K₁₃.re) * (K₂₄.re * K₂₄.re) := by ring
        _ = 1 / 36 := by rw [a₃, a₄]; norm_num
    linear_combination this
  have sw : (w - 1 / 6) * (w + 1 / 6) = 0 := by
    have : w * w = 1 / 36 := by
      simp only [w]
      calc K₁₄.re * K₂₃.re * (K₁₄.re * K₂₃.re) = (K₁₄.re * K₁₄.re) * (K₂₃.re * K₂₃.re) := by ring
        _ = 1 / 36 := by rw [a₅, a₆]; norm_num
    linear_combination this
  rcases mul_eq_zero.mp sx with hx | hx <;> rcases mul_eq_zero.mp sy with hy | hy <;>
    rcases mul_eq_zero.mp sw with hw | hw <;> linarith

end

end Grading

/-- Complex phases of graded plane coefficients. -/
theorem noRealPlaneCoordinates : Statements.NoRealPlaneCoordinates := by
  intro ρ hρ ψ hψP hnorm _ hreal
  exact Grading.no_real_coordinates hρ ψ hψP hnorm hreal

end

end ThirteenPlanes.AlbertGrading
