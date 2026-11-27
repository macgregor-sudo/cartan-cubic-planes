module

public import ThirteenPlanes.AlbertGrading.Grading.GradedPlanes

@[expose] public section

/-! # Structure constants of normalized elements

For normalized `a ∈ A_g`, `b ∈ A_h` with `g, h` independent, `a ∘ b = κ c` with `c` normalized in
`A_{g+h}` and `|κ| = 1/2`. The proof uses only the quartic identity: with
`N(a,b) = ⟨a∘b, \overline{a∘b}⟩`, the instance `(a, b, ā, b̄)` gives `N(a,b) + N(a,b̄) = 3/2`,
and associativity of the trace form identifies the values on the three triples through `a`. -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

/-- `N(a,b) = ⟨a∘b, \overline{a∘b}⟩`. -/
def prodNorm (a b : JC) : ℂ := ip (mul a b) (conj (mul a b))

theorem ip_conj_normalized {u : JC} (hun : IsNormalized u) : ip u (conj u) = 3 := by
  rw [show ip u (conj u) = ip (mul u (conj u)) one by rw [ip_mul_assoc, JC.mul_one], hun.2,
    ip_one_one]

theorem conj_normalized {u : JC} (hun : IsNormalized u) : IsNormalized (conj u) :=
  ⟨by rw [conj_mul_conj_of_normalized hun, conj_conj], by rw [conj_conj, JC.mul_comm]; exact hun.2⟩

section

variable (hρ : IsTernaryGrading ρ)
include hρ

theorem prodNorm_pair {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0) (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0)
    {a b : JC} (ha : a ∈ charSpace ρ g) (han : IsNormalized a) (hb : b ∈ charSpace ρ h)
    (hbn : IsNormalized b) : prodNorm a b + prodNorm a (conj b) = 3 / 2 := by
  have hab := conj_mem_charSpace ha
  have hbb := conj_mem_charSpace hb
  have q := quartic_eq_zero a b (conj a) (conj b) (tr_eq_zero_of_mem hρ hg ha)
    (tr_eq_zero_of_mem hρ hh hb) (tr_eq_zero_of_mem hρ (neg_ne_zero.mpr hg) hab)
    (tr_eq_zero_of_mem hρ (neg_ne_zero.mpr hh) hbb)
  have e1 : ip a b = 0 := ip_eq_zero_of_charSpace hρ ha hb h₁
  have e2 : ip (conj a) (conj b) = 0 := by rw [ip_conj, e1, star_zero]
  have e3 : ip a (conj b) = 0 := ip_eq_zero_of_charSpace hρ ha hbb (by rwa [← sub_eq_add_neg])
  have e4 : ip b (conj a) = 0 := ip_eq_zero_of_charSpace hρ hb hab
    (by rw [← sub_eq_add_neg, ← neg_sub]; exact neg_ne_zero.mpr h₂)
  have m1 : mul b (conj a) = conj (mul a (conj b)) := by
    rw [conj_mul, conj_conj, JC.mul_comm]
  simp only [quartic, ← conj_mul, han.2, hbn.2, m1, ip_one_one, e1, e2, e3, e4,
    ip_conj_normalized han, ip_conj_normalized hbn] at q
  unfold prodNorm
  linear_combination q

theorem prodNorm_symm {g h : Charge}
    {a b c : JC} (ha : a ∈ charSpace ρ g) (hb : b ∈ charSpace ρ h) (hbn : IsNormalized b)
    (hc : c ∈ charSpace ρ (g + h)) (hcn : IsNormalized c) :
    prodNorm a b = prodNorm a (conj c) := by
  obtain ⟨κ, hκ⟩ := exists_smul_of_mem hρ hc (ne_zero_of_normalized hcn) (mul_mem_charSpace hρ ha hb)
  have hcb : mul a (conj c) ∈ charSpace ρ (-h) := by
    have := mul_mem_charSpace hρ ha (conj_mem_charSpace hc)
    rwa [neg_add, ← add_assoc, add_neg_cancel, zero_add] at this
  obtain ⟨κ', hκ'⟩ := exists_smul_of_mem hρ (conj_mem_charSpace hb)
    (conj_ne_zero (ne_zero_of_normalized hbn)) hcb
  have hk : κ = κ' := by
    have e : ip (mul a b) (conj c) = ip (mul a (conj c)) b := by
      rw [ip_mul_assoc, ip_mul_assoc, JC.mul_comm (conj c) b]
    rw [hκ, hκ', ip_smul_left, ip_smul_left, ip_conj_normalized hcn, ip_comm (conj b),
      ip_conj_normalized hbn] at e
    linear_combination e / 3
  unfold prodNorm
  rw [hκ, hκ', conj_smul, conj_smul, conj_conj, ip_smul_left, ip_smul_right, ip_smul_left,
    ip_smul_right, ip_conj_normalized hcn, ip_comm (conj b), ip_conj_normalized hbn, hk]

/-- `N(a,b) = 3/4` for normalized elements of independent grades. -/
theorem prodNorm_eq {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0) (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0)
    {a b : JC} (ha : a ∈ charSpace ρ g) (han : IsNormalized a) (hb : b ∈ charSpace ρ h)
    (hbn : IsNormalized b) : prodNorm a b = 3 / 4 := by
  obtain ⟨d, hd, hdn⟩ := exists_normalized hρ h₁
  obtain ⟨e, he, hen⟩ := exists_normalized hρ h₂
  have z1 : g + (g + h) ≠ 0 := by
    rw [← add_assoc, charge_add_self, ← sub_eq_neg_add, ← neg_sub]; exact neg_ne_zero.mpr h₂
  have z2 : g - (g + h) ≠ 0 := by rw [sub_add_cancel_left]; exact neg_ne_zero.mpr hh
  have z3 : g + (g - h) ≠ 0 := by
    rw [← add_sub_assoc, charge_add_self, sub_eq_add_neg, ← neg_add]; exact neg_ne_zero.mpr h₁
  have z4 : g - (g - h) ≠ 0 := by rw [sub_sub_cancel]; exact hh
  -- the three pair equations
  have eq1 := prodNorm_pair hρ hg hh h₁ h₂ ha han hb hbn
  have eq2 := prodNorm_pair hρ hg h₁ z1 z2 ha han hd hdn
  have eq3 := prodNorm_pair hρ hg h₂ z3 z4 ha han he hen
  -- identifications
  have s1 : prodNorm a b = prodNorm a (conj d) := prodNorm_symm hρ ha hb hbn hd hdn
  have he' : conj e ∈ charSpace ρ (g + (g + h)) := by
    have := conj_mem_charSpace he
    rwa [show -(g - h) = g + (g + h) by
      rw [← add_assoc, charge_add_self]; abel] at this
  have s2 : prodNorm a d = prodNorm a e := by
    have := prodNorm_symm hρ ha hd hdn he' (conj_normalized hen)
    rwa [conj_conj] at this
  have hbb : conj b ∈ charSpace ρ (-h) := conj_mem_charSpace hb
  have he'' : e ∈ charSpace ρ (g + -h) := by rwa [← sub_eq_add_neg]
  have s3 : prodNorm a (conj b) = prodNorm a (conj e) :=
    prodNorm_symm hρ ha hbb (conj_normalized hbn) he'' hen
  linear_combination (eq1 + eq2 - eq3 + s1 - s2 - s3) / 2

/-- The structure constant of two normalized elements of independent grades has modulus `1/2`. -/
theorem structure_constant {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0) (h₁ : g + h ≠ 0)
    (h₂ : g - h ≠ 0) {a b c : JC} (ha : a ∈ charSpace ρ g) (han : IsNormalized a)
    (hb : b ∈ charSpace ρ h) (hbn : IsNormalized b) (hc : c ∈ charSpace ρ (g + h))
    (hcn : IsNormalized c) : ∃ κ : ℂ, mul a b = κ • c ∧ κ * star κ = 1 / 4 := by
  obtain ⟨κ, hκ⟩ := exists_smul_of_mem hρ hc (ne_zero_of_normalized hcn) (mul_mem_charSpace hρ ha hb)
  refine ⟨κ, hκ, ?_⟩
  have := prodNorm_eq hρ hg hh h₁ h₂ ha han hb hbn
  unfold prodNorm at this
  rw [hκ, conj_smul, ip_smul_left, ip_smul_right, ip_conj_normalized hcn] at this
  linear_combination this / 3

end

end

end ThirteenPlanes.AlbertGrading.Grading
