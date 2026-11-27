module

public import ThirteenPlanes.SignedStabilizer.Coefficients
public import ThirteenPlanes.Weyl

@[expose] public section

set_option backward.privateInPublic true

/-! The coefficient equations of an infinitesimal symmetry of `c_t` force a zero matrix when
`t³ ≠ 1`: the diagonal and opposite-grade entries vanish directly, and every other entry is
multiplied by `t³` around a cycle of three equations. -/

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

namespace SignedStabilizer

private theorem charge_three (x : Charge) : x + x + x = 0 := by
  funext i
  change x i + x i + x i = 0
  linear_combination x i * (by decide : (3 : ZMod 3) = 0)

theorem ctCoeff_eq_zero (t : ℝ) {i j k : NonzeroCharge} (h : i.val + j.val + k.val ≠ 0) :
    ctCoeff t i j k = 0 := by
  have hd : signedDiagonalCoefficient i j k = 0 := by
    unfold signedDiagonalCoefficient
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      exact absurd (charge_three _) h
    · rfl
  simp [ctCoeff, hd, signedCoefficient_zero_of_grade_sum_ne_zero i j k h]

theorem ctCoeff_diag (t : ℝ) (x : NonzeroCharge) : ctCoeff t x x x = 3 := by
  simp only [ctCoeff, signedDiagonalCoefficient, and_self, ↓reduceIte, signedCoefficient_diagonal]
  push_cast
  ring

theorem ctCoeff_swap₁₂ (t : ℝ) (i j k : NonzeroCharge) : ctCoeff t i j k = ctCoeff t j i k := by
  have hd : signedDiagonalCoefficient i j k = signedDiagonalCoefficient j i k := by
    unfold signedDiagonalCoefficient
    congr 1
    apply propext
    constructor <;> rintro ⟨rfl, rfl⟩ <;> simp
  simp only [ctCoeff, hd, signedCoefficient_swap_first i j k]

theorem ctCoeff_swap₂₃ (t : ℝ) (i j k : NonzeroCharge) : ctCoeff t i j k = ctCoeff t i k j := by
  have hd : signedDiagonalCoefficient i j k = signedDiagonalCoefficient i k j := by
    unfold signedDiagonalCoefficient
    congr 1
    apply propext
    constructor <;> rintro ⟨rfl, rfl⟩ <;> simp
  simp only [ctCoeff, hd, signedCoefficient_swap_last i j k]

theorem ctCoeff_offDiag (t : ℝ) {i j : NonzeroCharge} (k : NonzeroCharge) (h : i ≠ j) :
    ctCoeff t i j k = (t : ℂ) * signedCoefficient i j k := by
  simp [ctCoeff, signedDiagonalCoefficient, h]

/-- On a zero-sum triple of pairwise independent grades the coefficient cubes to `-27/8`. -/
theorem signedCoefficient_cube {p x q : NonzeroCharge} (hsum : p.val + x.val + q.val = 0)
    (hpx : p.val ≠ x.val) (hpnx : p.val ≠ -x.val) :
    signedCoefficient p x q ^ 3 = -27 / 8 := by
  have hdep : ¬ dependentGrades p.val x.val := by
    unfold dependentGrades
    simp only [p.property, x.property, hpx, hpnx, or_self, not_false_eq_true]
  have hm : gradeMetric (p.val + x.val) q.val = 3 := by simp [gradeMetric, hsum]
  rw [signedCoefficient, hm, gradedProductCoefficient]
  simp only [hdep, ↓reduceIte]
  have hc : (chargeRoot ^ (gradeExponent p.val x.val).val) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, chargeRoot_cube, one_pow]
  linear_combination (-27 / 8 : ℂ) * hc

private theorem sum_single (f : NonzeroCharge → ℂ) (y₀ : NonzeroCharge)
    (h : ∀ y, y ≠ y₀ → f y = 0) : ∑ y, f y = f y₀ :=
  Fintype.sum_eq_single y₀ h

private theorem collapse₁ (t : ℝ) (m : NonzeroCharge → ℂ) (a b y₀ : NonzeroCharge)
    (hy : y₀.val + a.val + b.val = 0) :
    ∑ y, m y * ctCoeff t y a b = m y₀ * ctCoeff t y₀ a b := by
  apply sum_single
  intro y hne
  rw [ctCoeff_eq_zero t, mul_zero]
  intro h
  apply hne
  apply Subtype.ext
  linear_combination h - hy

private theorem collapse₂ (t : ℝ) (m : NonzeroCharge → ℂ) (a b y₀ : NonzeroCharge)
    (hy : y₀.val + a.val + b.val = 0) :
    ∑ y, m y * ctCoeff t a y b = m y₀ * ctCoeff t a y₀ b := by
  simp only [ctCoeff_swap₁₂ t a _ b]
  exact collapse₁ t m a b y₀ hy

private theorem collapse₃ (t : ℝ) (m : NonzeroCharge → ℂ) (a b y₀ : NonzeroCharge)
    (hy : y₀.val + a.val + b.val = 0) :
    ∑ y, m y * ctCoeff t a b y = m y₀ * ctCoeff t a b y₀ := by
  have e : ∀ y, ctCoeff t a b y = ctCoeff t y a b := fun y => by
    rw [ctCoeff_swap₂₃, ctCoeff_swap₁₂, ctCoeff_swap₂₃]
  simp only [e]
  exact collapse₁ t m a b y₀ hy

variable (t : ℝ) (m : Matrix NonzeroCharge NonzeroCharge ℂ)

/-- The insertion equations of a complex matrix for `c_t`. -/
def InsertEquations : Prop :=
  ∀ x x' x'', ∑ y, m y x * ctCoeff t y x' x'' + ∑ y, m y x' * ctCoeff t x y x'' +
    ∑ y, m y x'' * ctCoeff t x x' y = 0

/-- The skewness equations of a complex matrix for the opposite-grade pairing. -/
def SkewEquations : Prop :=
  ∀ x x', m (oppositeCharge x') x + m (oppositeCharge x) x' = 0

variable {t m}

theorem diag_entry_eq_zero (hE : InsertEquations t m) (x : NonzeroCharge) : m x x = 0 := by
  have h := hE x x x
  have hy : x.val + x.val + x.val = 0 := charge_three _
  rw [collapse₁ t (fun y => m y x) x x x hy, collapse₂ t (fun y => m y x) x x x hy,
    collapse₃ t (fun y => m y x) x x x hy, ctCoeff_diag] at h
  linear_combination h / 9

theorem opposite_entry_eq_zero (hS : SkewEquations m) (x : NonzeroCharge) :
    m (oppositeCharge x) x = 0 := by
  have h := hS x x
  linear_combination h / 2

theorem shifted_entry_eq_zero (ht : (t : ℂ) ^ 3 ≠ 1) (hE : InsertEquations t m)
    (x : NonzeroCharge) {s : Charge} (hs0 : s ≠ 0) (hsx : s ≠ x.val) (hsnx : s ≠ -x.val) :
    m ⟨x.val + s, fun h => hsnx (by linear_combination h)⟩ x = 0 := by
  set p : NonzeroCharge := ⟨x.val + s, fun h => hsnx (by linear_combination h)⟩ with hp
  set q : NonzeroCharge := ⟨x.val - s, fun h => hsx (by linear_combination -h)⟩ with hq
  have h3 := charge_three x.val
  have h3s := charge_three s
  -- zero-sum relations
  have r1 : p.val + x.val + q.val = 0 := by simp only [hp, hq]; linear_combination h3
  have r2 : x.val + x.val + x.val = 0 := h3
  have r3 : q.val + q.val + q.val = 0 := charge_three _
  have r4 : p.val + p.val + p.val = 0 := charge_three _
  have r1' : x.val + q.val + p.val = 0 := by linear_combination r1
  have r1'' : q.val + p.val + x.val = 0 := by linear_combination r1
  have E1 := hE x x q
  rw [collapse₁ t (fun y => m y x) x q p r1, collapse₂ t (fun y => m y x) x q p r1,
    collapse₃ t (fun y => m y q) x x x r2, ctCoeff_diag] at E1
  have E2 := hE q q p
  rw [collapse₁ t (fun y => m y q) q p x r1', collapse₂ t (fun y => m y q) q p x r1',
    collapse₃ t (fun y => m y p) q q q r3, ctCoeff_diag] at E2
  have E3 := hE p p x
  rw [collapse₁ t (fun y => m y p) p x q r1'', collapse₂ t (fun y => m y p) p x q r1'',
    collapse₃ t (fun y => m y x) p p p r4, ctCoeff_diag] at E3
  -- all off-diagonal coefficients are the same
  have hpx : p ≠ x := fun h => hs0 (by
    have := congrArg Subtype.val h; simp only [hp] at this; linear_combination this)
  have k1 : ctCoeff t x p q = ctCoeff t p x q := ctCoeff_swap₁₂ t x p q
  have k2 : ctCoeff t x q p = ctCoeff t p x q := by rw [ctCoeff_swap₂₃, k1]
  have k3 : ctCoeff t q x p = ctCoeff t p x q := by rw [ctCoeff_swap₁₂, k2]
  have k4 : ctCoeff t q p x = ctCoeff t p x q := by rw [ctCoeff_swap₂₃, k3]
  have k5 : ctCoeff t p q x = ctCoeff t p x q := by rw [ctCoeff_swap₁₂, k4]
  simp only [k1, k2, k3, k4, k5] at E1 E2 E3
  have hκ : ctCoeff t p x q = (t : ℂ) * signedCoefficient p x q := ctCoeff_offDiag t q hpx
  have hσ : signedCoefficient p x q ^ 3 = -27 / 8 := by
    apply signedCoefficient_cube r1
    · intro h; apply hs0; simp only [hp] at h; linear_combination h
    · intro h; apply hsx; simp only [hp] at h; linear_combination h - h3
  rw [hκ] at E1 E2 E3
  set a := m p x
  set b := m x q
  set d := m q p
  set σ := signedCoefficient p x q
  have key : (27 : ℂ) * a * (1 - (t : ℂ) ^ 3) = 0 := by
    linear_combination 9 * E3 - 6 * ((t : ℂ) * σ) * E2 + 4 * ((t : ℂ) * σ) ^ 2 * E1 -
      8 * (t : ℂ) ^ 3 * a * hσ
  have h1 : (1 - (t : ℂ) ^ 3) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have : (27 : ℂ) * a = 0 := (mul_eq_zero.mp key).resolve_right h1
  simpa using this

/-- For `t³ ≠ 1` the only complex matrix solving the insertion and skewness equations is zero. -/
theorem matrix_eq_zero (ht : (t : ℂ) ^ 3 ≠ 1) (hE : InsertEquations t m)
    (hS : SkewEquations m) : m = 0 := by
  ext y x
  rw [Matrix.zero_apply]
  by_cases hyx : y = x
  · subst hyx; exact diag_entry_eq_zero hE y
  by_cases hyo : y = oppositeCharge x
  · subst hyo; exact opposite_entry_eq_zero hS x
  have h3 := charge_three x.val
  have hs0 : y.val - x.val ≠ 0 := fun h => hyx (Subtype.ext (by linear_combination h))
  have hsx : y.val - x.val ≠ x.val := fun h => hyo (Subtype.ext (by
    change y.val = -x.val; linear_combination h + h3))
  have hsnx : y.val - x.val ≠ -x.val := fun h => y.property (by linear_combination h)
  have := shifted_entry_eq_zero ht hE x hs0 hsx hsnx
  have hy : (⟨x.val + (y.val - x.val), fun h => hsnx (by linear_combination h)⟩ : NonzeroCharge)
      = y := Subtype.ext (by ring)
  rwa [hy] at this

end SignedStabilizer

end

end ThirteenPlanes
