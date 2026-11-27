module

public import ThirteenPlanes.AlbertGrading.Grading.Cubic
public import ThirteenPlanes.AlbertGrading.Grading.PhasesMain

@[expose] public section

/-! # graded cubic expansion, (S1): the three-plane coefficients lie in `-(3/2) μ₃`

With a conjugation-consistent normalized family `U_{-k} = Ū_k`, put `c(a,b,d) = -(2/3)⟨U_a∘U_b, U_d⟩`.
The quartic identity on `(U_a, U_a, U_b, U_{a-b})` gives `c(b,a-b,-a) = c(a,b,-(a+b)) c(a,a-b,a+b)`;
three instances and `|c| = 1` give `c³ = 1`. Arbitrary normalized elements differ by cube roots of unity.
-/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

open Classical in
/-- A conjugation-consistent normalized element of each nonzero grade. -/
def gU (hρ : IsTernaryGrading ρ) (k : Charge) : JC :=
  if hk : k = 0 then one else
    if (pointOf hk).val.val = k then pointUnit hρ (pointOf hk) else conj (pointUnit hρ (pointOf hk))

variable (hρ : IsTernaryGrading ρ)
include hρ

theorem gU_spec {k : Charge} (hk : k ≠ 0) : gU hρ k ∈ charSpace ρ k ∧ IsNormalized (gU hρ k) := by
  obtain ⟨hu, hun⟩ := pointUnit_spec hρ (pointOf hk)
  unfold gU; rw [dif_neg hk]
  split_ifs with h
  · rw [h] at hu; exact ⟨hu, hun⟩
  · have hr := (pointOf_rep hk).resolve_left h
    refine ⟨?_, conj_normalized hun⟩
    rw [hr] at hu
    have := conj_mem_charSpace hu; rwa [neg_neg] at this

theorem gU_neg {k : Charge} (hk : k ≠ 0) : gU hρ (-k) = conj (gU hρ k) := by
  have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
  have hne : -k ≠ k := charge_neg_ne_self hk
  unfold gU; rw [dif_neg hk, dif_neg hk']
  have hp : pointOf hk' = pointOf hk := pointOf_neg hk
  simp only [hp]
  rcases pointOf_rep hk with h | h <;> rw [h] <;> simp [hne, Ne.symm hne]

/-- The normalized coefficient. -/
def cU (a b d : Charge) : ℂ := -(2 / 3 : ℂ) * ip (mul (gU hρ a) (gU hρ b)) (gU hρ d)

omit hρ in
theorem D_swap23 (x y z : JC) : ip (mul x y) z = ip (mul x z) y := by
  rw [ip_mul_assoc, ip_mul_assoc, JC.mul_comm y z]

theorem cU_swap12 (a b d : Charge) : cU hρ a b d = cU hρ b a d := by
  unfold cU; rw [JC.mul_comm]

theorem cU_swap23 (a b d : Charge) : cU hρ a b d = cU hρ a d b := by
  unfold cU; rw [D_swap23]

theorem cU_neg {a b d : Charge} (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    cU hρ (-a) (-b) (-d) = star (cU hρ a b d) := by
  unfold cU
  rw [gU_neg hρ ha, gU_neg hρ hb, gU_neg hρ hd, ← conj_mul, ip_conj, star_mul']
  congr 1; simp

theorem cU_norm {a b : Charge} (ha : a ≠ 0) (hb : b ≠ 0) (h₁ : a + b ≠ 0) (h₂ : a - b ≠ 0) :
    cU hρ a b (-(a + b)) * star (cU hρ a b (-(a + b))) = 1 := by
  have := cubic_three_modulus hρ ha hb h₁ h₂ (gU_spec hρ ha).1 (gU_spec hρ ha).2
    (gU_spec hρ hb).1 (gU_spec hρ hb).2 (gU_spec hρ (neg_ne_zero.mpr h₁)).1
    (gU_spec hρ (neg_ne_zero.mpr h₁)).2
  unfold cU
  rw [star_mul', show star (-(2 / 3 : ℂ)) = -(2 / 3) by simp]
  linear_combination (4 / 9 : ℂ) * this

/-- The quartic relation. -/
theorem cU_rel {a b : Charge} (ha : a ≠ 0) (hb : b ≠ 0) (h₁ : a + b ≠ 0) (h₂ : a - b ≠ 0) :
    cU hρ b (a - b) (-a) = cU hρ a b (-(a + b)) * cU hρ a (a - b) (a + b) := by
  obtain ⟨m₁, n₁⟩ := gU_spec hρ ha
  obtain ⟨m₂, n₂⟩ := gU_spec hρ hb
  obtain ⟨m₃, n₃⟩ := gU_spec hρ h₂
  obtain ⟨m₄, n₄⟩ := gU_spec hρ h₁
  have e2a : a + a ≠ 0 := charge_add_self_ne_zero ha
  have e3 : a + (a - b) ≠ 0 := by
    rw [show a + (a - b) = -(a + b) by
      funext i; have : ∀ x y : ZMod 3, x + (x - y) = -(x + y) := by decide
      exact this (a i) (b i)]
    exact neg_ne_zero.mpr h₁
  have q := quartic_eq_zero _ _ _ _ (tr_eq_zero_of_mem hρ ha m₁) (tr_eq_zero_of_mem hρ ha m₁)
    (tr_eq_zero_of_mem hρ hb m₂) (tr_eq_zero_of_mem hρ h₂ m₃)
  unfold quartic at q
  obtain ⟨κ, hκ⟩ := exists_smul_of_mem hρ m₄ (ne_zero_of_normalized n₄) (mul_mem_charSpace hρ m₁ m₂)
  have hκv : κ * 3 = ip (mul (gU hρ a) (gU hρ b)) (gU hρ (-(a + b))) := by
    rw [hκ, ip_smul_left, gU_neg hρ h₁, ip_conj_normalized n₄]
  have z1 := ip_eq_zero_of_charSpace hρ m₁ m₁ e2a
  have z2 := ip_eq_zero_of_charSpace hρ m₁ m₂ h₁
  have z3 := ip_eq_zero_of_charSpace hρ m₁ m₃ e3
  have t1 : ip (conj (gU hρ a)) (mul (gU hρ b) (gU hρ (a - b))) =
      ip (mul (gU hρ b) (gU hρ (a - b))) (gU hρ (-a)) := by rw [ip_comm, gU_neg hρ ha]
  have t2 : ip (gU hρ (a + b)) (mul (gU hρ a) (gU hρ (a - b))) =
      ip (mul (gU hρ a) (gU hρ (a - b))) (gU hρ (a + b)) := ip_comm _ _
  simp only [hκ, n₁.1, ip_smul_left, ip_smul_right, z1, z2, z3, t1, t2] at q
  unfold cU
  rw [← hκv]
  linear_combination (-(2 / 3 : ℂ)) * q
