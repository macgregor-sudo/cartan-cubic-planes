module

public import ThirteenPlanes.Quaternionic.Heron

@[expose] public section

set_option backward.privateInPublic true

/-! Equality in the two-discriminant scalar bound for the quaternionic floor. -/

namespace QuaternionicMUB.Heron

/-- The balance vector is an ordering of `(b, 0, -b)` at the extremal square. -/
def FloorBalanceShape (x y z : ℝ) : Prop :=
  ∃ b : ℝ, b ^ 2 = 2 * Real.sqrt 3 - 3 ∧
    ((x = 0 ∧ y = b ∧ z = -b) ∨ (x = b ∧ y = 0 ∧ z = -b) ∨
      (x = b ∧ y = -b ∧ z = 0))

private theorem product_eq_abs_sum_iff (P R : ℝ) (hR : |R| ≤ 1) :
    P * R = |P + 3 * R| ↔ P = 0 ∧ R = 0 := by
  constructor
  · intro h
    have hnonneg : 0 ≤ P * R := h.symm ▸ abs_nonneg (P + 3 * R)
    have hzero : P * R = 0 := by
      by_contra hne
      have hp : 0 < P * R := lt_of_le_of_ne hnonneg (fun h0 => hne h0.symm)
      rcases mul_pos_iff.mp hp with ⟨hp, hr⟩ | ⟨hp, hr⟩
      · have hbound : 0 ≤ 1 - R := sub_nonneg.mpr (abs_le.mp hR).2
        have hprod := mul_nonneg hp.le hbound
        rw [abs_of_pos (by linarith)] at h
        nlinarith only [h, hprod, hr]
      · have hbound : 0 ≤ 1 + R := by linarith [(abs_le.mp hR).1]
        have hprod := mul_nonneg (neg_nonneg.mpr hp.le) hbound
        rw [abs_of_neg (by linarith)] at h
        nlinarith only [h, hprod, hr]
    have hsum : P + 3 * R = 0 := abs_eq_zero.mp (h.symm.trans hzero)
    rcases mul_eq_zero.mp hzero with hp | hr
    · exact ⟨hp, by linarith⟩
    · exact ⟨by linarith, hr⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

private theorem inverse_sqrt_three : 1 / Real.sqrt 3 = Real.sqrt 3 / 3 := by
  have hs := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have hpos := Real.sqrt_pos.2 (show 0 < (3 : ℝ) by norm_num)
  field_simp [hpos.ne']
  nlinarith only [hs]

/-- The exact equality set of the scalar bound under the two signed discriminants. -/
theorem floor_equality_of_discriminants (x y z : ℝ)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1)
    (hp : 0 ≤ discriminant ((1 + x) / 2) ((1 + y) / 2) ((1 + z) / 2))
    (hm : 0 ≤ discriminant ((1 - x) / 2) ((1 - y) / 2) ((1 - z) / 2)) :
    (3 + (x * y + y * z + z * x)) / 6 = 1 - 1 / Real.sqrt 3 ↔
      FloorBalanceShape x y z := by
  constructor
  · intro h
    let P := x + y + z
    let S := x * y + y * z + z * x
    let R := x * y * z
    have hxy : |x| * |y| ≤ 1 := by
      calc
        _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using hy
    have hR : |R| ≤ 1 := by
      calc
        _ = |x| * |y| * |z| := by simp only [R, abs_mul]
        _ ≤ 1 * |z| := mul_le_mul_of_nonneg_right hxy (abs_nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using hz
    have hS : S = 3 - 2 * Real.sqrt 3 := by
      change (3 + S) / 6 = _ at h
      rw [inverse_sqrt_three] at h
      linarith only [h]
    have hquad : S ^ 2 - 6 * S - 3 = 0 := by
      rw [hS]
      nlinarith only [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have hp_id : 16 * discriminant ((1 + x) / 2) ((1 + y) / 2) ((1 + z) / 2) =
        4 * P * R - (S ^ 2 - 6 * S - 3) + 4 * (P + 3 * R) := by
      dsimp only [P, S, R, discriminant]
      ring
    have hm_id : 16 * discriminant ((1 - x) / 2) ((1 - y) / 2) ((1 - z) / 2) =
        4 * P * R - (S ^ 2 - 6 * S - 3) - 4 * (P + 3 * R) := by
      dsimp only [P, S, R, discriminant]
      ring
    rw [hquad, sub_zero] at hp_id hm_id
    have heq : P * R = |P + 3 * R| := by
      apply le_antisymm (product_le_abs_sum P R hR)
      rcases le_total 0 (P + 3 * R) with hsign | hsign
      · rw [abs_of_nonneg hsign]
        linarith only [hm, hm_id]
      · rw [abs_of_nonpos hsign]
        linarith only [hp, hp_id]
    obtain ⟨hP, hR0⟩ := (product_eq_abs_sum_iff P R hR).mp heq
    change x + y + z = 0 at hP
    change x * y * z = 0 at hR0
    change x * y + y * z + z * x = 3 - 2 * Real.sqrt 3 at hS
    rcases mul_eq_zero.mp hR0 with hxy | hz0
    · rcases mul_eq_zero.mp hxy with hx0 | hy0
      · have hzy : z = -y := by linarith only [hP, hx0]
        rw [hx0, hzy] at hS
        exact ⟨y, by nlinarith only [hS], Or.inl ⟨hx0, rfl, hzy⟩⟩
      · have hzx : z = -x := by linarith only [hP, hy0]
        rw [hy0, hzx] at hS
        exact ⟨x, by nlinarith only [hS], Or.inr (Or.inl ⟨rfl, hy0, hzx⟩)⟩
    · have hyx : y = -x := by linarith only [hP, hz0]
      rw [hz0, hyx] at hS
      exact ⟨x, by nlinarith only [hS], Or.inr (Or.inr ⟨rfl, hyx, hz0⟩)⟩
  · rintro ⟨b, hb, hshape⟩
    rw [inverse_sqrt_three]
    rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      nlinarith only [hb]

/-- Equality in the scalar share formula for every pair of normalized coefficient
triples with the two zero autocorrelations. -/
theorem floor_equality_of_autocorrelations (a b : Fin 3 → ℂ)
    (hu : ∀ i, Complex.normSq (a i) + Complex.normSq (b i) = 1)
    (ha : correlation a = 0) (hb : correlation b = 0) :
    let z := fun i => Complex.normSq (a i) - Complex.normSq (b i)
    (3 + (z 0 * z 1 + z 1 * z 2 + z 2 * z 0)) / 6 = 1 - 1 / Real.sqrt 3 ↔
      FloorBalanceShape (z 0) (z 1) (z 2) := by
  let z := fun i => Complex.normSq (a i) - Complex.normSq (b i)
  have hbound (i : Fin 3) : |z i| ≤ 1 := by
    apply abs_le.mpr
    dsimp only [z]
    constructor <;> linarith [hu i, Complex.normSq_nonneg (a i), Complex.normSq_nonneg (b i)]
  have hplus (i : Fin 3) : (1 + z i) / 2 = Complex.normSq (a i) := by
    dsimp only [z]
    linarith only [hu i]
  have hminus (i : Fin 3) : (1 - z i) / 2 = Complex.normSq (b i) := by
    dsimp only [z]
    linarith only [hu i]
  apply floor_equality_of_discriminants (z 0) (z 1) (z 2) (hbound 0) (hbound 1) (hbound 2)
  · rw [hplus, hplus, hplus]
    exact discriminant_nonneg_of_correlation (a 0) (a 1) (a 2) ha
  · rw [hminus, hminus, hminus]
    exact discriminant_nonneg_of_correlation (b 0) (b 1) (b 2) hb

end QuaternionicMUB.Heron
