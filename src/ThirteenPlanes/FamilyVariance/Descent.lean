module

public import ThirteenPlanes.FamilyVariance.Formula
public import ThirteenPlanes.Basins.Invariant

@[expose] public section

/-! Descent of the relative variance of the field energy along the planar one-loop flow.

Along any solution of `u' = familyField lam ε u` with `u ≠ 0`, the relative variance `D` of the
field energy of `a D + b C` has derivative `-κ w² / (16π² W³)`, where `w = b²(a-b)(a+lam b)` is the
wedge polynomial and `W = a² + 3 lam b²`. It is strictly negative exactly off the three stationary
lines `b = 0`, `a = b`, `a = -lam b`; these lines are invariant, so along every solution starting off
them `D` is strictly decreasing on `[0, ∞)`, whether or not the strength is at a fixed value. -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {P : CubicPair V} {lam ε : ℝ}

/-- The ratio of `u` is one of the three stationary ratios `t = 0, 1, -1/lam` (as lines). -/
def StationaryRatio (lam : ℝ) (u : ℝ × ℝ) : Prop := u.2 = 0 ∨ u.1 = u.2 ∨ u.1 = -lam * u.2

/-- The rate of change of `D` along the planar flow: `-κ w² / (16π² W³)`. -/
def anisotropyFlowRate (n lam : ℝ) (u : ℝ × ℝ) : ℝ :=
  -(anisotropySlope n lam) * ratioWedge lam u ^ 2 / (flowScale * weightedStrength lam u.1 u.2 ^ 3)

theorem anisotropySlope_twentySix : anisotropySlope 26 2 = 21 / 5 := by
  norm_num [anisotropySlope]

theorem anisotropyFlowRate_neg_iff {n : ℝ} (hn : 0 < n) (hlam : 0 < lam) {u : ℝ × ℝ}
    (hu : u ≠ 0) : anisotropyFlowRate n lam u < 0 ↔ ¬ StationaryRatio lam u := by
  have hW := weightedStrength_pos hlam (a := u.1) (b := u.2) (by simpa using hu)
  have hk := anisotropySlope_pos hn hlam
  rw [StationaryRatio, ← ratioWedge_eq_zero_iff, anisotropyFlowRate, neg_mul, neg_div,
    neg_lt_zero]
  have hden : 0 < flowScale * weightedStrength lam u.1 u.2 ^ 3 :=
    mul_pos flowScale_pos (pow_pos hW 3)
  rw [div_pos_iff_of_pos_right hden]
  constructor
  · intro h hw; rw [hw] at h; simp at h
  · intro hw; exact mul_pos hk (by positivity)

theorem anisotropyFlowRate_eq_zero_iff {n : ℝ} (hn : 0 < n) (hlam : 0 < lam) {u : ℝ × ℝ}
    (hu : u ≠ 0) : anisotropyFlowRate n lam u = 0 ↔ StationaryRatio lam u := by
  rw [StationaryRatio, ← ratioWedge_eq_zero_iff, anisotropyFlowRate]
  have hW := weightedStrength_pos hlam (a := u.1) (b := u.2) (by simpa using hu)
  have hk := anisotropySlope_pos hn hlam
  have hden : 0 < flowScale * weightedStrength lam u.1 u.2 ^ 3 :=
    mul_pos flowScale_pos (pow_pos hW 3)
  rw [div_eq_zero_iff, or_iff_left hden.ne', mul_eq_zero, neg_eq_zero, or_iff_right hk.ne',
    pow_eq_zero_iff two_ne_zero]

/-- Derivative of the rational function `D` along any flow line, within any set. -/
theorem anisotropyRational_hasDerivWithinAt_flow {n : ℝ} (hn : 0 < n) (hlam : 0 < lam)
    {x : ℝ → ℝ × ℝ} {s : ℝ} {S : Set ℝ}
    (hx : HasDerivWithinAt x (familyField lam ε (x s)) S s) (hxs : x s ≠ 0) :
    HasDerivWithinAt (fun r ↦ anisotropyRational n lam (x r))
      (anisotropyFlowRate n lam (x s)) S s := by
  have hW := weightedStrength_pos hlam (a := (x s).1) (b := (x s).2) (by simpa using hxs)
  have h := hasDerivWithinAt_anisotropyRational (n := n) (lam := lam) (by linarith)
    (by linarith) hx.fst hx.snd hW.ne'
  refine h.congr_deriv ?_
  have hw := familyField_wedge lam ε (x s).1 (x s).2
  have hwedge : (x s).1 * (familyField lam ε (x s)).2 - (x s).2 * (familyField lam ε (x s)).1 =
      ratioWedge lam (x s) / flowScale := by
    rw [eq_div_iff flowScale_ne_zero, mul_comm, ratioWedge]
    simpa using hw
  rw [hwedge, anisotropyAngular, anisotropyFlowRate]
  field_simp

variable [Nontrivial V]

/-- **Rate of change along the flow.** Along a solution of the planar one-loop flow with
`u(s) ≠ 0`, the relative variance of the field energy has derivative `-κ w² / (16π² W³)` at `s`
(right derivative at `s = 0`). -/
theorem familyAnisotropy_hasDerivWithinAt_flow (hlaws : HasContractionLaws P lam)
    (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree) (hlam : 0 < lam)
    {x : ℝ → ℝ × ℝ} (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    {s : ℝ} (hs : 0 ≤ s) (hxs : x s ≠ 0) :
    HasDerivWithinAt (fun r ↦ familyAnisotropy P (x r))
      (anisotropyFlowRate (Module.finrank ℝ V) lam (x s)) (Ici 0) s := by
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  have hfun : (fun r ↦ familyAnisotropy P (x r)) =
      fun r ↦ anisotropyRational (Module.finrank ℝ V) lam (x r) := by
    funext r; exact familyAnisotropy_eq hlaws hD hC (x r)
  rw [hfun]
  exact anisotropyRational_hasDerivWithinAt_flow hn hlam (hx s hs) hxs

/-- **Strict decrease off the stationary ratios.** Along a solution with `u(s) ≠ 0`, the
derivative of the relative variance of the field energy is strictly negative exactly when the
ratio at time `s` is not one of the three stationary ratios. -/
theorem familyAnisotropy_flow_deriv_neg_iff (hlaws : HasContractionLaws P lam)
    (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree) (hlam : 0 < lam)
    {x : ℝ → ℝ × ℝ} (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    {s : ℝ} (hs : 0 ≤ s) (hxs : x s ≠ 0) :
    ∃ r, HasDerivWithinAt (fun r ↦ familyAnisotropy P (x r)) r (Ici 0) s ∧
      (r < 0 ↔ ¬ StationaryRatio lam (x s)) ∧ (r = 0 ↔ StationaryRatio lam (x s)) := by
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  exact ⟨_, familyAnisotropy_hasDerivWithinAt_flow hlaws hD hC hlam hx hs hxs,
    anisotropyFlowRate_neg_iff hn hlam hxs, anisotropyFlowRate_eq_zero_iff hn hlam hxs⟩

omit [FiniteDimensional ℝ V] [Nontrivial V] in
/-- The complement of the stationary lines is invariant under the forward flow. -/
theorem not_stationaryRatio_of_solution (hlam : 0 < lam)
    {x : ℝ → ℝ × ℝ} (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (h0 : ¬ StationaryRatio lam (x 0)) : ∀ s, 0 ≤ s → ¬ StationaryRatio lam (x s) ∧ x s ≠ 0 := by
  simp only [StationaryRatio, not_or] at h0
  obtain ⟨hb, hab, hc⟩ := h0
  intro s hs
  have hb' := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb s hs
  have hab' := ne_zero_of_pos_mul (diagonalGap_eq_pos_mul hx)
    (sub_ne_zero.mpr (Ne.symm hab)) s hs
  have hc' := ne_zero_of_pos_mul (thirdGap_eq_pos_mul hlam.ne' hx)
    (fun h => hc (by linarith)) s hs
  refine ⟨?_, fun h => hb' (by rw [h]; rfl)⟩
  simp only [StationaryRatio, not_or]
  refine ⟨hb', fun h => hab' (by rw [h]; ring), fun h => hc' (by rw [h]; ring)⟩

/-- **Monotone descent.** Along every forward solution of the planar one-loop flow starting off the
three stationary lines, the relative variance of the field energy is strictly decreasing on
`[0, ∞)`. -/
theorem familyAnisotropy_strictAntiOn (hlaws : HasContractionLaws P lam)
    (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree) (hlam : 0 < lam)
    {x : ℝ → ℝ × ℝ} (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (h0 : ¬ StationaryRatio lam (x 0)) :
    StrictAntiOn (fun s ↦ familyAnisotropy P (x s)) (Ici 0) := by
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  have hinv := not_stationaryRatio_of_solution hlam hx h0
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun r ↦ familyAnisotropy P (x r))
      (anisotropyFlowRate (Module.finrank ℝ V) lam (x s)) (Ici 0) s := fun s hs =>
    familyAnisotropy_hasDerivWithinAt_flow hlaws hD hC hlam hx hs (hinv s hs).2
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) (fun s hs => (hd s hs).continuousWithinAt)
  intro s hs
  rw [interior_Ici] at hs
  have hs' : (0 : ℝ) ≤ s := (mem_Ioi.mp hs).le
  rw [((hd s hs').hasDerivAt (Ici_mem_nhds (mem_Ioi.mp hs))).deriv]
  exact (anisotropyFlowRate_neg_iff hn hlam (hinv s hs').2).mpr (hinv s hs').1

/-- **Descent from weak positive mixing.** Along every forward solution starting with ratio
`0 < t < 1`, the relative variance of the field energy is strictly decreasing on `[0, ∞)`. -/
theorem familyAnisotropy_strictAntiOn_of_ratio (hlaws : HasContractionLaws P lam)
    (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree) (hlam : 0 < lam)
    {x : ℝ → ℝ × ℝ} (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (ha : (x 0).1 ≠ 0) (ht0 : 0 < (x 0).2 / (x 0).1) (ht1 : (x 0).2 / (x 0).1 < 1) :
    StrictAntiOn (fun s ↦ familyAnisotropy P (x s)) (Ici 0) := by
  refine familyAnisotropy_strictAntiOn hlaws hD hC hlam hx ?_
  simp only [StationaryRatio, not_or]
  set a := (x 0).1
  set b := (x 0).2
  refine ⟨fun hb => by rw [hb, zero_div] at ht0; exact lt_irrefl _ ht0,
    fun hab => by rw [← hab, div_self ha] at ht1; exact lt_irrefl _ ht1, fun hc => ?_⟩
  have hb : b ≠ 0 := fun hb => by rw [hb, zero_div] at ht0; exact lt_irrefl _ ht0
  have e : b / (-lam * b) = -(1 / lam) := by field_simp
  rw [hc, e] at ht0
  have : 0 < 1 / lam := by positivity
  linarith

end

end ThirteenPlanes
