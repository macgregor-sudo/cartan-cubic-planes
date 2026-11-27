module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

/-! Elementary one-variable lemmas for forward solutions on `[0, ∞)`.

Throughout, a scalar function `y` is differentiable within `Ici 0` at every point of `Ici 0`;
this gives continuity on `Ici 0` and right derivatives everywhere. -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

section Calculus

variable {y y' : ℝ → ℝ}

theorem continuousOn_Ici_of_hasDerivWithinAt
    (hy : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' s) (Ici 0) s) :
    ContinuousOn y (Ici 0) :=
  fun s hs ↦ (hy s hs).continuousWithinAt

theorem hasDerivWithinAt_Ici_self
    (hy : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' s) (Ici 0) s) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt y (y' s) (Ici s) s :=
  (hy s hs).mono (Ici_subset_Ici.mpr hs)

/-- A function whose derivative is negative whenever it exceeds `C` by at most `w > 0` stays at
most `C`, provided it starts at most `C`. -/
theorem le_of_deriv_neg_above {C w : ℝ} (hw : 0 < w)
    (hy : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' s) (Ici 0) s) (h0 : y 0 ≤ C)
    (hneg : ∀ s, 0 ≤ s → C < y s → y s ≤ C + w → y' s < 0) :
    ∀ t, 0 ≤ t → y t ≤ C := by
  intro t ht
  have hcont := continuousOn_Ici_of_hasDerivWithinAt hy
  have key : ∀ η, 0 < η → η ≤ w → y t ≤ C + η := by
    intro η hη hηw
    have := image_le_of_deriv_right_lt_deriv_boundary (a := 0) (b := t) (f := y) (f' := y')
      (hcont.mono Icc_subset_Ici_self)
      (fun s hs ↦ hasDerivWithinAt_Ici_self hy hs.1)
      (B := fun _ ↦ C + η) (B' := fun _ ↦ 0) (by linarith)
      (fun _ ↦ hasDerivAt_const _ _)
      (fun s hs hys ↦ hneg s hs.1 (by linarith) (by linarith))
      ⟨ht, le_rfl⟩
    simpa using this
  by_contra hlt
  rw [not_le] at hlt
  have h1 := key (min w ((y t - C) / 2)) (lt_min hw (by linarith)) (min_le_left _ _)
  have h2 := min_le_right w ((y t - C) / 2)
  linarith

/-- A function whose derivative is positive whenever it lies below `c` by at most `w > 0` stays
at least `c`, provided it starts at least `c`. -/
theorem ge_of_deriv_pos_below {c w : ℝ} (hw : 0 < w)
    (hy : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' s) (Ici 0) s) (h0 : c ≤ y 0)
    (hpos : ∀ s, 0 ≤ s → y s < c → c - w ≤ y s → 0 < y' s) :
    ∀ t, 0 ≤ t → c ≤ y t := by
  have := le_of_deriv_neg_above (y := fun s ↦ -y s) (y' := fun s ↦ -y' s) (C := -c) hw
    (fun s hs ↦ (hy s hs).neg) (by linarith)
    (fun s hs h1 h2 ↦ by have := hpos s hs (by linarith) (by linarith); linarith)
  intro t ht
  have := this t ht
  linarith

/-- A function with nonnegative derivative on `Ici 0` is monotone there. -/
theorem monotoneOn_Ici_of_deriv_nonneg
    (hy : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' s) (Ici 0) s)
    (hpos : ∀ s, 0 ≤ s → 0 ≤ y' s) : MonotoneOn y (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (continuousOn_Ici_of_hasDerivWithinAt hy)
  · intro s hs
    rw [interior_Ici] at hs ⊢
    exact ((hy s (mem_Ici.mpr (mem_Ioi.mp hs).le)).mono Ioi_subset_Ici_self)
  · intro s hs
    rw [interior_Ici] at hs
    exact hpos s (mem_Ioi.mp hs).le

/-- Monotone convergence with a speed bound: if `y` never exceeds `L`, has nonnegative
derivative, and has derivative bounded below by a positive constant as long as it stays below any
level `M < L`, then `y` converges to `L`. -/
theorem tendsto_of_deriv_nonneg_bounded {L : ℝ}
    (hy : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' s) (Ici 0) s)
    (hle : ∀ s, 0 ≤ s → y s ≤ L) (hpos : ∀ s, 0 ≤ s → 0 ≤ y' s)
    (hspeed : ∀ M < L, ∃ δ > 0, ∀ s, 0 ≤ s → y 0 ≤ y s → y s ≤ M → δ ≤ y' s) :
    Tendsto y atTop (𝓝 L) := by
  have hmono := monotoneOn_Ici_of_deriv_nonneg hy hpos
  rw [tendsto_order]
  refine ⟨fun M hM ↦ ?_, fun M hM ↦ ?_⟩
  · obtain ⟨δ, hδ, hsp⟩ := hspeed M hM
    filter_upwards [eventually_gt_atTop (max 0 ((M - y 0) / δ))] with s hs
    have hs0 : 0 ≤ s := le_trans (le_max_left _ _) hs.le
    by_contra hns
    rw [not_lt] at hns
    -- on `[0, s]` the function stays between `y 0` and `M`
    have hbelow : ∀ r ∈ Icc (0 : ℝ) s, y 0 ≤ y r ∧ y r ≤ M := fun r hr ↦
      ⟨hmono (mem_Ici.mpr le_rfl) hr.1 hr.1, le_trans (hmono hr.1 hs0 hr.2) hns⟩
    have hg : MonotoneOn (fun r ↦ y r - δ * r) (Icc 0 s) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun r ↦ y' r - δ) (convex_Icc 0 s)
      · exact ((continuousOn_Ici_of_hasDerivWithinAt hy).mono Icc_subset_Ici_self).sub
          (continuousOn_const.mul continuousOn_id)
      · intro r hr
        rw [interior_Icc] at hr ⊢
        have : HasDerivWithinAt y (y' r) (Ioo 0 s) r :=
          (hy r (mem_Ici.mpr (le_of_lt hr.1))).mono (Ioo_subset_Icc_self.trans Icc_subset_Ici_self)
        have h2 := this.sub ((hasDerivWithinAt_id r (Ioo 0 s)).const_mul δ)
        simp only [mul_one] at h2
        exact h2
      · intro r hr
        rw [interior_Icc] at hr
        have hr' : r ∈ Icc (0 : ℝ) s := Ioo_subset_Icc_self hr
        have := hsp r hr'.1 (hbelow r hr').1 (hbelow r hr').2
        linarith
    have := hg ⟨le_rfl, hs0⟩ ⟨hs0, le_rfl⟩ hs0
    simp only [mul_zero, sub_zero] at this
    have h2 : (M - y 0) / δ < s := lt_of_le_of_lt (le_max_right _ _) hs
    rw [div_lt_iff₀ hδ] at h2
    nlinarith
  · filter_upwards [eventually_ge_atTop 0] with s hs
    exact lt_of_le_of_lt (hle s hs) hM

/-- A linear equation `v' = -c v + F` with `c > 0` and convergent forcing `F → Finf` has
`v → Finf / c`. -/
theorem tendsto_of_forced_linear {v F : ℝ → ℝ} {c Finf : ℝ} (hc : 0 < c)
    (hv : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt v (-c * v s + F s) (Ici 0) s)
    (hF : Tendsto F atTop (𝓝 Finf)) : Tendsto v atTop (𝓝 (Finf / c)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set η₁ := c * η / 4 with hη₁
  have hη₁pos : 0 < η₁ := by positivity
  obtain ⟨s₀', hs₀'⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hF η₁ hη₁pos)
  set s₀ := max 0 s₀'
  have hs₀ : 0 ≤ s₀ := le_max_left _ _
  have hFclose : ∀ s, s₀ ≤ s → |F s - Finf| < η₁ := fun s hs ↦ by
    simpa [Real.dist_eq] using hs₀' s (le_trans (le_max_right _ _) hs)
  set E₀ := |v s₀ - Finf / c|
  set B : ℝ → ℝ := fun s ↦ (E₀ + 1) * Real.exp (-c * (s - s₀)) + η₁ / c with hB
  have hBderiv : ∀ s, HasDerivAt B (-c * B s + η₁) s := by
    intro s
    have h1 : HasDerivAt (fun s ↦ -c * (s - s₀)) (-c * 1) s :=
      ((hasDerivAt_id s).sub_const s₀).const_mul (-c)
    have h2 := ((h1.exp).const_mul (E₀ + 1)).add_const (η₁ / c)
    convert h2 using 1
    simp only [hB]
    field_simp
    ring
  -- the two-sided bound `|v - Finf/c| ≤ B` from `s₀` on
  have hbound : ∀ s, s₀ ≤ s → |v s - Finf / c| ≤ B s := by
    intro s hs
    have hcont : ContinuousOn v (Icc s₀ s) :=
      (continuousOn_Ici_of_hasDerivWithinAt hv).mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hs₀))
    have hder : ∀ r ∈ Ico s₀ s, HasDerivWithinAt v (-c * v r + F r) (Ici r) r :=
      fun r hr ↦ hasDerivWithinAt_Ici_self hv (le_trans hs₀ hr.1)
    have hB0 : E₀ < B s₀ := by
      simp only [hB, sub_self, mul_zero, Real.exp_zero, mul_one]
      have : 0 < η₁ / c := by positivity
      linarith
    have up := image_le_of_deriv_right_lt_deriv_boundary (a := s₀) (b := s)
      (f := fun r ↦ v r - Finf / c) (f' := fun r ↦ -c * v r + F r)
      (hcont.sub continuousOn_const) (fun r hr ↦ (hder r hr).sub_const _)
      (B := B) (B' := fun r ↦ -c * B r + η₁)
      (le_trans (le_abs_self _) hB0.le) hBderiv
      (fun r hr hEq ↦ by
        have hFr := (abs_lt.mp (hFclose r hr.1)).2
        rw [← hEq]
        field_simp
        linarith)
      ⟨hs, le_rfl⟩
    have down := image_le_of_deriv_right_lt_deriv_boundary (a := s₀) (b := s)
      (f := fun r ↦ -(v r - Finf / c)) (f' := fun r ↦ -(-c * v r + F r))
      ((hcont.sub continuousOn_const).neg) (fun r hr ↦ ((hder r hr).sub_const _).neg)
      (B := B) (B' := fun r ↦ -c * B r + η₁)
      (le_trans (neg_le_abs _) hB0.le) hBderiv
      (fun r hr hEq ↦ by
        have hFr := (abs_lt.mp (hFclose r hr.1)).1
        rw [← hEq]
        field_simp
        linarith)
      ⟨hs, le_rfl⟩
    exact abs_le.mpr ⟨by linarith, up⟩
  -- the bound tends to `η / 4`
  have hexp : Tendsto (fun s ↦ (E₀ + 1) * Real.exp (-c * (s - s₀))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s ↦ c * (s - s₀)) atTop atTop :=
      Tendsto.const_mul_atTop hc (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (E₀ + 1)
    simpa [Function.comp_def, neg_mul] using h2
  filter_upwards [eventually_ge_atTop s₀,
    hexp.eventually (gt_mem_nhds (show (0 : ℝ) < η / 4 by positivity))] with s hs hsmall
  rw [Real.dist_eq]
  have := hbound s hs
  have hηc : η₁ / c = η / 4 := by rw [hη₁]; field_simp
  simp only [hB, hηc] at this
  linarith

/-- A linear equation with multiplicative rate keeps the sign of its solution: if
`y' = y * c` on `Ici 0` with `c` continuous there, then `y t` is a positive multiple of `y 0`. -/
theorem exists_pos_mul_of_multiplicative {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    (hy : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt y (y s * c s) (Ici 0) s) :
    ∀ t, 0 ≤ t → ∃ k > 0, y t = k * y 0 := by
  set c' : ℝ → ℝ := fun s ↦ c (max 0 s)
  have hc' : Continuous c' :=
    hc.comp_continuous (continuous_const.max continuous_id) (fun s ↦ le_max_left 0 s)
  set C : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, c' s
  have hC : ∀ t, HasDerivAt C (c' t) t := fun t ↦
    (hc'.integral_hasStrictDerivAt 0 t).hasDerivAt
  set z : ℝ → ℝ := fun t ↦ y t * Real.exp (-C t)
  have hz : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt z 0 (Ici 0) s := by
    intro s hs
    have h1 := (hy s hs).mul ((hC s).neg.exp.hasDerivWithinAt (s := Ici 0))
    have hcs : c' s = c s := by simp [c', max_eq_right (show (0 : ℝ) ≤ s from hs)]
    convert h1 using 1
    rw [hcs]
    ring
  intro t ht
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := t)
    ((continuousOn_Ici_of_hasDerivWithinAt hz).mono Icc_subset_Ici_self)
    (fun s hs ↦ hasDerivWithinAt_Ici_self hz hs.1) t ⟨ht, le_rfl⟩
  refine ⟨Real.exp (C t), Real.exp_pos _, ?_⟩
  have hC0 : C 0 = 0 := by simp [C]
  simp only [z, hC0, neg_zero, Real.exp_zero, mul_one] at hconst
  calc y t = y t * Real.exp (-C t) * Real.exp (C t) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = Real.exp (C t) * y 0 := by rw [hconst, mul_comm]

/-- A continuous function on `Ici 0` that never vanishes keeps the sign of its value at `0`. -/
theorem pos_of_continuousOn_ne_zero (hy : ContinuousOn y (Ici 0))
    (hne : ∀ s, 0 ≤ s → y s ≠ 0) (h0 : 0 < y 0) : ∀ t, 0 ≤ t → 0 < y t := by
  intro t ht
  by_contra hneg
  rw [not_lt] at hneg
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' ht (hy.mono Icc_subset_Ici_self)
    ⟨hneg, h0.le⟩
  exact hne r hr.1 hr0

end Calculus

end

end ThirteenPlanes
