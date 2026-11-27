module

public import ThirteenPlanes.AlbertGrading.Grading.CharacterSpaces
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-! # ternary grading theorem (ii): the normalized element of each nonzero character line

For `0 ≠ x ∈ A_g`, `x ∘ x̄ = λ e` with `3λ = ⟨x, x̄⟩ > 0` and `x ∘ x = κ x̄`; the quartic identity on
`(x, x, x̄, x̄)` gives `|κ|² = λ`, and `u = t x` with `t³ = 1/(λκ)` is normalized. Two normalized
elements of `A_g` differ by a cube root of unity. -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

theorem charge_add_self (g : Charge) : g + g = -g := by
  funext i
  have h : ∀ a : ZMod 3, a + a = -a := by decide
  exact h (g i)

theorem charge_neg_ne_self {g : Charge} (hg : g ≠ 0) : -g ≠ g := by
  intro h
  apply hg
  funext i
  have h' : ∀ a : ZMod 3, -a = a → a = 0 := by decide
  exact h' (g i) (congrFun h i)

theorem charge_add_self_ne_zero {g : Charge} (hg : g ≠ 0) : g + g ≠ 0 := by
  rw [charge_add_self]; exact neg_ne_zero.mpr hg

theorem conj_ne_zero {z : JC} (hz : z ≠ 0) : conj z ≠ 0 := by
  intro h; apply hz; rw [← conj_conj z, h, conj_zero]

theorem ne_zero_of_normalized {u : JC} (hu : IsNormalized u) : u ≠ 0 := by
  intro h; apply JC.one_ne_zero; rw [← hu.2, h, mul_zero_left]

theorem conj_mul_conj_of_normalized {u : JC} (hu : IsNormalized u) : mul (conj u) (conj u) = u := by
  rw [← conj_mul, hu.1, conj_conj]

/-- The three cube roots of unity are the values of `chargePhase`. -/
theorem exists_chargePhase_of_cube {c : ℂ} (hc : c ^ 3 = 1) : ∃ a : ZMod 3, c = chargePhase a := by
  have hq := chargeRoot_quadratic
  have hfac : (c - 1) * (c - chargeRoot) * (c - chargeRoot ^ 2) = 0 := by
    linear_combination hc + (c - 1) * (chargeRoot - 1 - c) * hq
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by rw [chargePhase_zero]; exact sub_eq_zero.mp h⟩
    · exact ⟨1, by rw [sub_eq_zero.mp h]; show _ = chargeRoot ^ (1 : ZMod 3).val; rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]⟩
  · exact ⟨2, by rw [sub_eq_zero.mp h]; show _ = chargeRoot ^ (2 : ZMod 3).val; rw [show (2 : ZMod 3).val = 2 from rfl]⟩

section Grading

variable (hρ : IsTernaryGrading ρ)
include hρ

/-- Existence of a normalized element of `A_g`, `g ≠ 0`. -/
theorem exists_normalized {g : Charge} (hg : g ≠ 0) : ∃ u ∈ charSpace ρ g, IsNormalized u := by
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem hρ g
  have hxb : conj x ∈ charSpace ρ (-g) := conj_mem_charSpace hx
  have hxb0 : conj x ≠ 0 := conj_ne_zero hx0
  -- `x ∘ x̄ = λ e`
  have hm0 : mul x (conj x) ∈ charSpace ρ 0 := by
    have := mul_mem_charSpace hρ hx hxb
    rwa [add_neg_cancel] at this
  obtain ⟨c, hc⟩ := exists_smul_of_mem hρ (one_mem_charSpace_zero hρ) one_ne_zero hm0
  -- `x ∘ x = κ x̄`
  have hm1 : mul x x ∈ charSpace ρ (-g) := by
    have := mul_mem_charSpace hρ hx hx
    rwa [charge_add_self] at this
  obtain ⟨κ, hκ⟩ := exists_smul_of_mem hρ hxb hxb0 hm1
  set P := ip x (conj x) with hP
  have hPpos : 0 < P.re := ip_conj_self_pos hx0
  have hPim : P.im = 0 := ip_conj_self_im x
  have hcP : c * 3 = P := by
    have h1 : ip (mul x (conj x)) one = P := by rw [ip_mul_assoc, mul_one]
    rw [hc, ip_smul_left, ip_one_one] at h1
    exact h1
  have hxx : ip x x = 0 := ip_eq_zero_of_charSpace hρ hx hx (charge_add_self_ne_zero hg)
  have hxbxb : ip (conj x) (conj x) = 0 := by rw [ip_conj, hxx, star_zero]
  have hmbb : mul (conj x) (conj x) = star κ • x := by
    rw [← conj_mul, hκ, conj_smul, conj_conj]
  have htr := tr_eq_zero_of_mem hρ hg hx
  have htrb := tr_eq_zero_of_mem hρ (neg_ne_zero.mpr hg) hxb
  have hq := quartic_eq_zero x x (conj x) (conj x) htr htr htrb htrb
  simp only [quartic, hκ, hmbb, hc, ip_smul_left, ip_smul_right, ip_one_one, hxx, hxbxb,
    ip_comm (conj x) x, ← hP] at hq
  -- `κ κ̄ P = P²/3`
  have hP0 : P ≠ 0 := fun h => by rw [h] at hPpos; simp at hPpos
  have hκκ : κ * star κ = c := by
    have h2 : P * (κ * star κ - c) = 0 := by
      have e : c = P / 3 := by rw [← hcP]; ring
      rw [e] at hq ⊢
      linear_combination hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hP0)
  have hc0 : c ≠ 0 := by
    intro h; apply hP0; rw [← hcP, h, zero_mul]
  have hκ0 : κ ≠ 0 := by
    intro h; apply hc0; rw [← hκκ, h, zero_mul]
  -- `c` is a positive real
  have hcre : c = (c.re : ℂ) := by
    apply Complex.ext
    · simp
    · have : (c * 3).im = 0 := by rw [hcP]; exact hPim
      simp at this
      simpa using this
  have hcpos : 0 < c.re := by
    have : (c * 3).re = P.re := by rw [hcP]
    simp at this
    linarith
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (c * κ)⁻¹ (by norm_num : 0 < 3)
  have htcκ : t ^ 3 * (c * κ) = 1 := by rw [ht]; exact inv_mul_cancel₀ (mul_ne_zero hc0 hκ0)
  have ht0 : t ≠ 0 := by
    rintro rfl; simp at htcκ
  have hcstar : star c = c := by
    rw [hcre]; exact Complex.conj_ofReal _
  -- `|t|² λ = 1`
  have hm : t * star t * c = 1 := by
    have hstar : star t ^ 3 * (c * star κ) = 1 := by
      have := congrArg star htcκ
      rw [star_mul', star_pow, star_mul', hcstar, star_one] at this
      exact this
    have hcube : (t * star t * c) ^ 3 = 1 := by
      calc (t * star t * c) ^ 3 = (t ^ 3 * (c * κ)) * (star t ^ 3 * (c * star κ)) := by
            linear_combination (-(t ^ 3 * star t ^ 3 * c ^ 2)) * hκκ
        _ = 1 := by rw [htcκ, hstar, _root_.one_mul]
    have hreal : t * star t * c = ((Complex.normSq t * c.re : ℝ) : ℂ) := by
      rw [show star t = (starRingEnd ℂ) t from rfl, Complex.mul_conj]
      nth_rewrite 1 [hcre]
      push_cast; ring
    rw [hreal] at hcube ⊢
    have hnn : 0 ≤ Complex.normSq t * c.re := mul_nonneg (Complex.normSq_nonneg t) hcpos.le
    have : Complex.normSq t * c.re = 1 := by
      have h3 : (Complex.normSq t * c.re) ^ 3 = 1 := by exact_mod_cast hcube
      exact (pow_eq_one_iff_of_nonneg hnn (by norm_num)).mp h3
    rw [this]; simp
  have htκ : t ^ 2 * κ = star t := by
    have h1 : t * (t ^ 2 * κ - star t) * c = 0 := by linear_combination htcκ - hm
    rcases mul_eq_zero.mp h1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h ht0
      · exact sub_eq_zero.mp h
    · exact absurd h hc0
  refine ⟨t • x, Submodule.smul_mem _ t hx, ?_, ?_⟩
  · rw [mul_smul_left, mul_smul_right, hκ, smul_smul, smul_smul, conj_smul]
    rw [show t * t * κ = star t by rw [← htκ]; ring]
  · rw [conj_smul, mul_smul_left, mul_smul_right, hc, smul_smul, smul_smul]
    rw [hm, one_smul]

/-- Uniqueness up to cube roots of unity. -/
theorem normalized_unique {g : Charge} {u v : JC} (hu : u ∈ charSpace ρ g) (hun : IsNormalized u)
    (hv : v ∈ charSpace ρ g) (hvn : IsNormalized v) : ∃ a : ZMod 3, v = chargePhase a • u := by
  obtain ⟨c, rfl⟩ := exists_smul_of_mem hρ hu (ne_zero_of_normalized hun) hv
  have hub0 : conj u ≠ 0 := conj_ne_zero (ne_zero_of_normalized hun)
  have h1 : c ^ 2 = star c := by
    have e := hvn.1
    rw [mul_smul_left, mul_smul_right, hun.1, smul_smul, conj_smul] at e
    have : (c * c - star c) • conj u = 0 := by rw [sub_smul, e, sub_self]
    have := (smul_eq_zero.mp this).resolve_right hub0
    rw [sq]; exact sub_eq_zero.mp this
  have h2 : c * star c = 1 := by
    have e := hvn.2
    rw [conj_smul, mul_smul_left, mul_smul_right, hun.2, smul_smul] at e
    have : (c * star c - 1) • one = 0 := by rw [sub_smul, e, one_smul, sub_self]
    have := (smul_eq_zero.mp this).resolve_right JC.one_ne_zero
    exact sub_eq_zero.mp this
  obtain ⟨a, ha⟩ := exists_chargePhase_of_cube (c := c)
    (by rw [pow_succ, h1, _root_.mul_comm, h2])
  exact ⟨a, by rw [ha]⟩

end Grading

end

end ThirteenPlanes.AlbertGrading.Grading
