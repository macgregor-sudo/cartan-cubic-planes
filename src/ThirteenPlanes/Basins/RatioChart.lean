module

public import ThirteenPlanes.Basins.MixingChart

@[expose] public section

/-! The basin of the decoupled fixed point, in the chart `t = b/a`.

For initial ratio `-1/lam < t ≤ 0` the solution keeps `a ≠ 0` and `-1/lam < t ≤ 0`; there
`K t' = a² t² (1 - t)(1 + lam t) ≥ 0`, so `t` increases to `0` (or stays at `0`). -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

/-- Lower bound for `a²` from the weighted strength in the chart `t = b/a`. -/
theorem ratio_sq_lower {lam Rlo B a b : ℝ} (ha : a ≠ 0) (hR : Rlo ≤ weightedStrength lam a b)
    (hB : (b / a) ^ 2 ≤ B) (hlam : 0 ≤ lam) (hpos : 0 < 1 + 3 * lam * B) :
    Rlo / (1 + 3 * lam * B) ≤ a ^ 2 := by
  rw [div_le_iff₀ hpos]
  have e : weightedStrength lam a b = a ^ 2 + 3 * lam * (a ^ 2 * (b / a) ^ 2) := by
    unfold weightedStrength; field_simp
  have := mul_le_mul_of_nonneg_left hB (sq_nonneg a)
  have h3 := mul_le_mul_of_nonneg_left this (show 0 ≤ 3 * lam by linarith)
  rw [e] at hR
  nlinarith

/-- Initial ratio in `(-1/lam, 0]` keeps `a ≠ 0` and the ratio in `(-1/lam, 0]`, and the ratio
tends to `0`. -/
theorem tendsto_ratio_zero (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (ha0 : (x 0).1 ≠ 0) (hlo : -1 / lam < (x 0).2 / (x 0).1) (hhi : (x 0).2 / (x 0).1 ≤ 0) :
    (∀ s, 0 ≤ s → (x s).1 ≠ 0) ∧
    (∀ s, 0 ≤ s → -1 / lam < (x s).2 / (x s).1 ∧ (x s).2 / (x s).1 ≤ 0) ∧
    Tendsto (fun s ↦ (x s).2 / (x s).1) atTop (𝓝 0) := by
  have hlam0 : 0 < lam := by linarith
  set t : ℝ → ℝ := fun s ↦ (x s).2 / (x s).1 with ht_def
  have hlt0 : 0 < lam * t 0 + 1 := by
    have := (div_lt_iff₀ hlam0).mp (show -1 / lam < t 0 from hlo)
    linarith
  have hbt : ∀ s, (x s).1 ≠ 0 → (x s).2 = (x s).1 * t s := fun s has ↦ by
    simp only [t]; field_simp
  have hq0 : (x 0).2 * (lam * (x 0).2 + (x 0).1) ≤ 0 := by
    rw [hbt 0 ha0]
    have : (x 0).1 * t 0 * (lam * ((x 0).1 * t 0) + (x 0).1) =
        (x 0).1 ^ 2 * (t 0 * (lam * t 0 + 1)) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (mul_nonpos_of_nonpos_of_nonneg hhi hlt0.le)
  have hg0 : lam * (x 0).2 + (x 0).1 ≠ 0 := by
    rw [hbt 0 ha0]
    have : lam * ((x 0).1 * t 0) + (x 0).1 = (x 0).1 * (lam * t 0 + 1) := by ring
    rw [this]
    exact mul_ne_zero ha0 hlt0.ne'
  have hq : ∀ s, 0 ≤ s → (x s).2 * (lam * (x s).2 + (x s).1) ≤ 0 := fun s hs ↦ by
    obtain ⟨k, hk, e⟩ := sectorQ_eq_pos_mul hlam0.ne' hx s hs
    rw [e]; exact mul_nonpos_of_nonneg_of_nonpos hk.le hq0
  have hg := ne_zero_of_pos_mul (thirdGap_eq_pos_mul hlam0.ne' hx) hg0
  have hx0 : x 0 ≠ 0 := fun h ↦ ha0 (by rw [h]; rfl)
  have hxne := ne_zero_of_solution hlam hε hx hx0
  have ha : ∀ s, 0 ≤ s → (x s).1 ≠ 0 := by
    intro s hs has
    have h1 := hq s hs
    rw [has, add_zero] at h1
    have hb : (x s).2 = 0 := by nlinarith [sq_nonneg (x s).2]
    exact hxne s hs (Prod.ext has hb)
  have hrange : ∀ s, 0 ≤ s → 0 < lam * t s + 1 ∧ t s ≤ 0 := by
    intro s hs
    have has := ha s hs
    have h1 := hq s hs
    have h2 := hg s hs
    rw [hbt s has] at h1 h2
    have e1 : (x s).1 * t s * (lam * ((x s).1 * t s) + (x s).1) =
        (x s).1 ^ 2 * (t s * (lam * t s + 1)) := by ring
    have e2 : lam * ((x s).1 * t s) + (x s).1 = (x s).1 * (lam * t s + 1) := by ring
    rw [e1] at h1
    rw [e2] at h2
    have hpa : 0 < (x s).1 ^ 2 := by positivity
    have hprod : t s * (lam * t s + 1) ≤ 0 := by
      by_contra hc; rw [not_le] at hc; nlinarith
    have hne : lam * t s + 1 ≠ 0 := fun h ↦ h2 (by rw [h, mul_zero])
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exfalso
      have : t s < 0 := by nlinarith
      nlinarith
    · exact ⟨hpos, by nlinarith⟩
  have hrange' : ∀ s, 0 ≤ s → -1 / lam < t s ∧ t s ≤ 0 := fun s hs ↦ by
    refine ⟨?_, (hrange s hs).2⟩
    rw [div_lt_iff₀ hlam0]
    linarith [(hrange s hs).1]
  refine ⟨ha, hrange', ?_⟩
  have ht' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt t
      ((x s).1 ^ 2 * ratioPolynomial lam (t s) / flowScale) (Ici 0) s := fun s hs ↦
    familyField_hasDerivWithinAt_ratio (ha s hs) (solution_fst hx s hs) (solution_snd hx s hs)
  rcases hhi.lt_or_eq with htneg | htz
  · obtain ⟨hRlo, hRle⟩ := weightedStrength_pos_lower_of_solution hlam hε hx hx0
    set Rlo := min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / 3)
    apply tendsto_of_deriv_nonneg_bounded ht' (fun s hs ↦ (hrange s hs).2)
    · intro s hs
      apply div_nonneg _ flowScale_pos.le
      apply mul_nonneg (sq_nonneg _)
      unfold ratioPolynomial
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith [(hrange s hs).2]))
        (by linarith [(hrange s hs).1])
    · intro M hM
      have hpos : 0 < 1 + 3 * lam * t 0 ^ 2 := by positivity
      have hM2 : 0 < M ^ 2 := by nlinarith
      have hδ : 0 < Rlo / (1 + 3 * lam * t 0 ^ 2) * (M ^ 2 * (lam * t 0 + 1)) / flowScale :=
        div_pos (mul_pos (div_pos hRlo hpos) (mul_pos hM2 hlt0)) flowScale_pos
      refine ⟨_, hδ, ?_⟩
      intro s hs h0 hMs
      have hts := hrange s hs
      have hβ := ratio_sq_lower (ha s hs) (hRle s hs) (B := t 0 ^ 2)
        (by change t s ^ 2 ≤ t 0 ^ 2; nlinarith) hlam0.le hpos
      have hrp : M ^ 2 * (lam * t 0 + 1) ≤ ratioPolynomial lam (t s) := by
        unfold ratioPolynomial
        have h1 : M ^ 2 ≤ t s ^ 2 * (1 - t s) := by nlinarith
        have h2 : lam * t 0 + 1 ≤ 1 + lam * t s := by nlinarith
        exact mul_le_mul h1 h2 hlt0.le (by nlinarith)
      apply div_le_div_of_nonneg_right _ flowScale_pos.le
      exact mul_le_mul hβ hrp (mul_nonneg (sq_nonneg _) hlt0.le)
        (le_trans (div_pos hRlo hpos).le hβ)
  · have hb0 : (x 0).2 = 0 := by
      exact (div_eq_zero_iff.mp htz).resolve_right ha0
    have hb := decoupled_invariant hx hb0
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    simp [t, hb s hs]

/-- The coordinate of the decoupled fixed point, `√(K ε)`. -/
def decoupledLevel (ε : ℝ) : ℝ := Real.sqrt (flowScale * ε)

/-- Every forward solution with initial ratio in `(-1/lam, 0]` converges to the decoupled fixed
point on the side of its initial sign of `a`. -/
theorem tendsto_decoupled_point (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (ha0 : (x 0).1 ≠ 0) (hlo : -1 / lam < (x 0).2 / (x 0).1) (hhi : (x 0).2 / (x 0).1 ≤ 0) :
    (0 < (x 0).1 → Tendsto x atTop (𝓝 (decoupledLevel ε, 0))) ∧
    ((x 0).1 < 0 → Tendsto x atTop (𝓝 (-decoupledLevel ε, 0))) := by
  obtain ⟨ha, -, ht⟩ := tendsto_ratio_zero hlam hε hx ha0 hlo hhi
  have hsq := tendsto_diag_sq hε hx ha ht (by rw [strengthPolynomial_eq]; norm_num)
  rw [strengthPolynomial_eq] at hsq
  norm_num at hsq
  have hcont : ContinuousOn (fun s ↦ (x s).1) (Ici 0) := fun s hs ↦
    (solution_fst hx s hs).continuousWithinAt
  have hb : ∀ {c : ℝ}, Tendsto (fun s ↦ (x s).1) atTop (𝓝 c) →
      Tendsto (fun s ↦ (x s).2) atTop (𝓝 0) := fun {c} hac ↦ by
    have := ht.mul hac
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    exact div_mul_cancel₀ _ (ha s hs)
  refine ⟨fun hpos ↦ ?_, fun hneg ↦ ?_⟩
  · have hac := tendsto_of_sq_of_pos (pos_of_continuousOn_ne_zero hcont ha hpos) hsq
    exact hac.prodMk_nhds (hb hac)
  · have hneg' : ∀ s, 0 ≤ s → (x s).1 < 0 := by
      have := pos_of_continuousOn_ne_zero (y := fun s ↦ -(x s).1) hcont.neg
        (fun s hs ↦ neg_ne_zero.mpr (ha s hs)) (neg_pos.mpr hneg)
      exact fun s hs ↦ neg_pos.mp (this s hs)
    have hac := tendsto_of_sq_of_neg hneg' hsq
    exact hac.prodMk_nhds (hb hac)

end

end ThirteenPlanes
