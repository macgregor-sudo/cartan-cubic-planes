module

public import ThirteenPlanes.AlbertGrading.Grading.Phase

@[expose] public section

set_option backward.privateInPublic true

/-! # graded cubic expansion, (S1) concluded: `⟨u_g∘u_h,u_k⟩ ∈ -(3/2) μ₃` for every grading -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

private theorem cid (f : ZMod 3 → ZMod 3 → ZMod 3) (f' : ZMod 3 → ZMod 3 → ZMod 3)
    (h : ∀ x y, f x y = f' x y) (g h' : Charge) :
    (fun i => f (g i) (h' i)) = (fun i => f' (g i) (h' i)) := funext fun i => h _ _

variable (hρ : IsTernaryGrading ρ)
include hρ

theorem cU_cube {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0) (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0) :
    cU hρ g h (-(g + h)) ^ 3 = 1 := by
  have nh : -h ≠ 0 := neg_ne_zero.mpr hh
  have n1 : -(g + h) ≠ 0 := neg_ne_zero.mpr h₁
  have n2 : -(g - h) ≠ 0 := neg_ne_zero.mpr h₂
  have i1 : -h - g = -(g + h) := by abel
  have i2 : -(-h + g) = -(g - h) := by abel
  have i3 : -h + g = g - h := by abel
  have i4 : -(g + h) - h = -(g - h) := by
    funext i; have : ∀ x y : ZMod 3, -(x + y) - y = -(x - y) := by decide
    exact this (g i) (h i)
  have i5 : -(-(g + h) + h) = g := by abel
  have i6 : -(g + h) + h = -g := by abel
  have i7 : -(g + (g - h)) = g + h := by
    funext i; have : ∀ x y : ZMod 3, -(x + (x - y)) = x + y := by decide
    exact this (g i) (h i)
  set x := cU hρ g h (-(g + h))
  set y := cU hρ g (-h) (-(g - h))
  set z := cU hρ g (g - h) (g + h)
  set w := cU hρ h (g + h) (-(g - h))
  -- R1
  have R1 := cU_rel hρ hg hh h₁ h₂
  rw [cU_swap23, cU_swap12, show cU hρ (-g) h (g - h) = star y by
    rw [← cU_neg hρ hg nh n2, neg_neg, neg_neg]] at R1
  -- R2
  have R2 := cU_rel hρ nh hg (by rw [i3]; exact h₂) (by rw [i1]; exact n1)
  rw [i1, neg_neg, i2, cU_swap23 hρ g, cU_swap12 hρ (-h) g,
    show cU hρ (-h) (-(g + h)) (-h + g) = star w by
      rw [i3, ← cU_neg hρ hh h₁ n2, neg_neg]] at R2
  -- R3
  have R3 := cU_rel hρ n1 hh (by rw [i6]; exact neg_ne_zero.mpr hg) (by rw [i4]; exact n2)
  have L3 : cU hρ h (-(g - h)) (g + h) = w := cU_swap23 hρ _ _ _
  have M3 : cU hρ (-(g + h)) h g = x := by rw [cU_swap12, cU_swap23, cU_swap12]
  have N3 : cU hρ (-(g + h)) (-(g - h)) (-g) = star z := by
    rw [cU_swap12, cU_swap23, cU_swap12, ← cU_neg hρ hg h₂ h₁]
  rw [i4, neg_neg, i5, i6, L3, M3, N3] at R3
  have hz : z * star z = 1 := by
    have := cU_norm hρ hg h₂ (by rw [← neg_neg (g + (g - h)), i7]; exact n1)
      (by rw [sub_sub_cancel]; exact hh)
    rwa [i7] at this
  have hx : x * star x = 1 := cU_norm hρ hg hh h₁ h₂
  have hy : y = star x * star z := by
    have := congrArg star R1; rw [star_star, star_mul'] at this; exact this
  have hw : star w = star x * z := by
    rw [R3, star_mul', star_star]
  have e : x = star x ^ 2 := by
    calc x = y * star w := R2
      _ = star x * star z * (star x * z) := by rw [hy, hw]
      _ = star x ^ 2 * (z * star z) := by ring
      _ = star x ^ 2 := by rw [hz, _root_.mul_one]
  calc x ^ 3 = x ^ 2 * x := by ring
    _ = x ^ 2 * star x ^ 2 := by rw [← e]
    _ = (x * star x) ^ 2 := by ring
    _ = 1 := by rw [hx]; norm_num

/-- (S1): for every ternary grading group, normalized elements of three pairwise independent
grades with zero sum have `⟨a∘b, c⟩ = -(3/2) ω^φ`. -/
theorem phase_mu3 {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0) (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0)
    {a b c : JC} (ha : a ∈ charSpace ρ g) (han : IsNormalized a) (hb : b ∈ charSpace ρ h)
    (hbn : IsNormalized b) (hc : c ∈ charSpace ρ (-(g + h))) (hcn : IsNormalized c) :
    ∃ φ : ZMod 3, ip (mul a b) c = -(3 / 2 : ℂ) * chargePhase φ := by
  have n1 : -(g + h) ≠ 0 := neg_ne_zero.mpr h₁
  obtain ⟨i, rfl⟩ := normalized_unique hρ (gU_spec hρ hg).1 (gU_spec hρ hg).2 ha han
  obtain ⟨j, rfl⟩ := normalized_unique hρ (gU_spec hρ hh).1 (gU_spec hρ hh).2 hb hbn
  obtain ⟨l, rfl⟩ := normalized_unique hρ (gU_spec hρ n1).1 (gU_spec hρ n1).2 hc hcn
  obtain ⟨m, hm⟩ := exists_chargePhase_of_cube (cU_cube hρ hg hh h₁ h₂)
  refine ⟨i + j + l + m, ?_⟩
  have e : ip (mul (gU hρ g) (gU hρ h)) (gU hρ (-(g + h))) = -(3 / 2 : ℂ) * cU hρ g h (-(g + h)) := by
    unfold cU; ring
  simp only [mul_smul_left, mul_smul_right, ip_smul_left, ip_smul_right]
  rw [e, hm, chargePhase_add,
    chargePhase_add, chargePhase_add]
  ring
