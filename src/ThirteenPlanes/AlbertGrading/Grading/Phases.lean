module

public import ThirteenPlanes.AlbertGrading.Grading.Coefficients
public import ThirteenPlanes.AlbertGrading.Grading.GradedLines

@[expose] public section

/-! # no admissible coordinates make the three-plane coefficients real

For each isometry `ψ_p`, the coordinates have the form `ψ_p(ζ) = Re(ζ c_p)` with `c_p` a unit
multiple of a normalized element of `A_{±g_p}`. This uses only the norm condition. Real
coefficients force real structure constants `κ` with `κ² = 1/6` in this
scaling (`|κ| = 1/2` for normalized elements, `Coefficients.lean`), and the quartic identity on the
four grades `e₀, e₁, e₂, -(e₀+e₁+e₂)` gives `2(κκ' + κκ' + κκ') = 0`, impossible. 
-/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

/-- The cubic of `V` read in the complexification. -/
theorem apply_eq_ip (x y z : NativeTraceless) :
    nativeEqualCubic.apply x y z = (ip (mul (of x) (of y)) (of z)).re := by
  change Glennie.inner (Glennie.traceless (Glennie.jordan x y)) z = _
  rw [nativeInner_center_left, of_mul, inner_eq_ip_re]

section Coordinates

variable (ψ : SignedPlaneIndex → (ℂ →ₗ[ℝ] NativeTraceless))

/-- `c_p = ψ_p(1) - i ψ_p(i)`, so that `ψ_p(ζ) = Re(ζ c_p)`. -/
def coordElt (p : SignedPlaneIndex) : JC := ⟨(ψ p 1 : Glennie.Albert), -(ψ p Complex.I : Glennie.Albert)⟩

theorem of_psi (p : SignedPlaneIndex) (ζ : ℂ) :
    of (ψ p ζ : Glennie.Albert) =
      (1 / 2 : ℂ) • (ζ • coordElt ψ p + star ζ • conj (coordElt ψ p)) := by
  have hζ : ζ = ζ.re • (1 : ℂ) + ζ.im • Complex.I := by
    apply Complex.ext <;> simp
  have e : (ψ p ζ : Glennie.Albert) = ζ.re • (ψ p 1 : Glennie.Albert) +
      ζ.im • (ψ p Complex.I : Glennie.Albert) := by
    conv_lhs => rw [hζ]
    rw [map_add, map_smul, map_smul]; rfl
  rw [e]
  apply JC.ext
  · simp only [of_re, smul_re, smul_im, add_re, add_im, conj_re, conj_im, coordElt,
      Complex.conj_re, Complex.conj_im, Complex.star_def]
    norm_num
    module
  · simp only [of_im, smul_re, smul_im, add_re, add_im, conj_re, conj_im, coordElt,
      Complex.conj_re, Complex.conj_im, Complex.star_def]
    norm_num
    module

theorem coordElt_eq (p : SignedPlaneIndex) :
    coordElt ψ p = of (ψ p 1 : Glennie.Albert) - Complex.I • of (ψ p Complex.I : Glennie.Albert) := by
  apply JC.ext <;> simp [coordElt]

variable (hψP : ∀ p ζ, ψ p ζ ∈ pointPlane ρ p)
include hψP

theorem coordElt_mem (p : SignedPlaneIndex) :
    coordElt ψ p ∈ charSpace ρ p.val.val ⊔ charSpace ρ (-p.val.val) := by
  rw [coordElt_eq]
  exact Submodule.sub_mem _ (hψP p 1) (Submodule.smul_mem _ _ (hψP p Complex.I))

end Coordinates

section Norms

variable (ψ : SignedPlaneIndex → (ℂ →ₗ[ℝ] NativeTraceless))
  (hnorm : ∀ ζ : SignedPlaneIndex → ℂ, ‖∑ p, ψ p (ζ p)‖ ^ 2 = ∑ p, ‖ζ p‖ ^ 2)
include hnorm

theorem norm_psi (p : SignedPlaneIndex) (z : ℂ) : ‖ψ p z‖ ^ 2 = ‖z‖ ^ 2 := by
  have h := hnorm (Pi.single p z)
  rw [Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq, map_zero])
    (by simp), Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq]; simp)
    (by simp), Pi.single_eq_same] at h
  exact h

theorem inner_psi_self (p : SignedPlaneIndex) (z : ℂ) :
    Glennie.inner (ψ p z : Glennie.Albert) (ψ p z) = ‖z‖ ^ 2 := by
  rw [← norm_psi ψ hnorm p z, ← real_inner_self_eq_norm_sq]; rfl

theorem inner_psi_one_I (p : SignedPlaneIndex) :
    Glennie.inner (ψ p 1 : Glennie.Albert) (ψ p Complex.I) = 0 := by
  have h := inner_psi_self ψ hnorm p (1 + Complex.I)
  have h1 := inner_psi_self ψ hnorm p 1
  have h2 := inner_psi_self ψ hnorm p Complex.I
  rw [map_add, Submodule.coe_add, Glennie.inner_add_left, Glennie.inner_add_right,
    Glennie.inner_add_right, Glennie.inner_comm (ψ p Complex.I : Glennie.Albert)] at h
  have n1 : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; norm_num
  rw [n1, h1, h2] at h
  simp at h
  linarith

theorem ip_coordElt_conj (p : SignedPlaneIndex) : ip (coordElt ψ p) (conj (coordElt ψ p)) = 2 := by
  rw [ip_conj_self]
  simp only [coordElt, Glennie.inner_neg_left, Glennie.inner_neg_right, neg_neg]
  rw [inner_psi_self ψ hnorm, inner_psi_self ψ hnorm]
  simp
  norm_num

theorem ip_coordElt_self (p : SignedPlaneIndex) : ip (coordElt ψ p) (coordElt ψ p) = 0 := by
  apply Complex.ext
  · simp only [ip_re, coordElt, Glennie.inner_neg_left, Glennie.inner_neg_right, neg_neg]
    rw [inner_psi_self ψ hnorm, inner_psi_self ψ hnorm]; simp
  · simp only [ip_im, coordElt, Glennie.inner_neg_left, Glennie.inner_neg_right,
      Glennie.inner_comm (-(ψ p Complex.I : Glennie.Albert))]
    rw [inner_psi_one_I ψ hnorm]; simp

end Norms

/-! ## Classification of admissible coordinates -/

section Main

variable (hρ : IsTernaryGrading ρ) (ψ : SignedPlaneIndex → (ℂ →ₗ[ℝ] NativeTraceless))
  (hψP : ∀ p ζ, ψ p ζ ∈ pointPlane ρ p)
  (hnorm : ∀ ζ : SignedPlaneIndex → ℂ, ‖∑ p, ψ p (ζ p)‖ ^ 2 = ∑ p, ‖ζ p‖ ^ 2)

include hρ hψP hnorm in
theorem coordElt_cases (p : SignedPlaneIndex) :
    ∃ α : ℂ, (coordElt ψ p = α • pointUnit hρ p ∨ coordElt ψ p = α • conj (pointUnit hρ p)) ∧
      α * star α = 2 / 3 := by
  obtain ⟨hu, hun⟩ := pointUnit_spec hρ p
  set u := pointUnit hρ p
  have hg := rep_ne_zero p
  have hub := conj_mem_charSpace hu
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (coordElt_mem ψ hψP p)
  obtain ⟨α, rfl⟩ := exists_smul_of_mem hρ hu (ne_zero_of_normalized hun) ha
  obtain ⟨β, rfl⟩ := exists_smul_of_mem hρ hub (conj_ne_zero (ne_zero_of_normalized hun)) hb
  have i1 : ip u u = 0 := ip_eq_zero_of_charSpace hρ hu hu (charge_add_self_ne_zero hg)
  have i2 : ip (conj u) (conj u) = 0 := by rw [ip_conj, i1, star_zero]
  have i3 : ip u (conj u) = 3 := ip_conj_normalized hun
  have i4 : ip (conj u) u = 3 := by rw [ip_comm]; exact i3
  have e0 := ip_coordElt_self ψ hnorm p
  have e2 := ip_coordElt_conj ψ hnorm p
  rw [← hab] at e0 e2
  simp only [conj_add, conj_smul, conj_conj, ip_add_left, ip_add_right, ip_smul_left,
    ip_smul_right, i1, i2, i3, i4] at e0 e2
  have hαβ : α * β = 0 := by linear_combination e0 / 6
  rcases mul_eq_zero.mp hαβ with h | h
  · subst h
    refine ⟨β, Or.inr (by rw [← hab, zero_smul, zero_add]), ?_⟩
    linear_combination e2 / 3
  · subst h
    refine ⟨α, Or.inl (by rw [← hab, zero_smul, add_zero]), ?_⟩
    linear_combination e2 / 3

open Classical in
/-- The element of `{c_p, c̄_p}` in `A_k`, for the point `p` of `k`. -/
def basisElt (k : Charge) : JC :=
  if hk : k = 0 then 0 else
    if coordElt ψ (pointOf hk) ∈ charSpace ρ k then coordElt ψ (pointOf hk)
    else conj (coordElt ψ (pointOf hk))

include hρ hψP hnorm in
theorem basisElt_spec {k : Charge} (hk : k ≠ 0) :
    ∃ θ : ℂ, ∃ n ∈ charSpace ρ k, IsNormalized n ∧ basisElt (ρ := ρ) ψ k = θ • n ∧
      θ * star θ = 2 / 3 := by
  set p := pointOf hk
  obtain ⟨hu, hun⟩ := pointUnit_spec hρ p
  obtain ⟨α, hc, hα⟩ := coordElt_cases hρ ψ hψP hnorm p
  have hrep := pointOf_rep hk
  have hαs : star α * star (star α) = 2 / 3 := by rw [star_star, _root_.mul_comm]; exact hα
  have hk' : k ≠ -k := fun h => charge_neg_ne_self hk h.symm
  unfold basisElt
  rw [dif_neg hk]
  -- `u ∈ A_k` or `ū ∈ A_k`
  have hcases : (pointUnit hρ p ∈ charSpace ρ k ∧ conj (pointUnit hρ p) ∈ charSpace ρ (-k)) ∨
      (conj (pointUnit hρ p) ∈ charSpace ρ k ∧ pointUnit hρ p ∈ charSpace ρ (-k)) := by
    rcases hrep with h | h
    · left; rw [← h]; exact ⟨hu, conj_mem_charSpace hu⟩
    · right
      have h' : k = -p.val.val := by rw [h, neg_neg]
      rw [h']
      exact ⟨conj_mem_charSpace hu, by rw [neg_neg]; exact hu⟩
  have hne : ∀ z, z ≠ 0 → z ∈ charSpace ρ (-k) → z ∉ charSpace ρ k :=
    fun z hz h1 h2 => hz (charSpace_disjoint hk' h2 h1)
  have hα0 : α ≠ 0 := by intro h; rw [h] at hα; simp at hα; norm_num at hα
  have hu0 := ne_zero_of_normalized hun
  have hub0 := conj_ne_zero hu0
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc with hc | hc <;> rw [hc]
  · rw [if_pos (Submodule.smul_mem _ _ h1)]; exact ⟨α, _, h1, hun, rfl, hα⟩
  · rw [if_neg (hne _ (smul_ne_zero hα0 hub0) (Submodule.smul_mem _ _ h2)), conj_smul, conj_conj]
    exact ⟨star α, _, h1, hun, rfl, hαs⟩
  · rw [if_neg (hne _ (smul_ne_zero hα0 hu0) (Submodule.smul_mem _ _ h2)), conj_smul]
    exact ⟨star α, _, h1, conj_normalized hun, rfl, hαs⟩
  · rw [if_pos (Submodule.smul_mem _ _ h1)]
    exact ⟨α, _, h1, conj_normalized hun, rfl, hα⟩

end Main

end

end ThirteenPlanes.AlbertGrading.Grading
