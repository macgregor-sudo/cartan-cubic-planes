module

public import ThirteenPlanes.ChargeFixedAttraction
public import ThirteenPlanes.ChargeFixedContinuation
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

set_option backward.privateInPublic true

/-! Trapping and forward attraction in a fixed-manifold chart. -/

open Set Filter Metric
open scoped RealInnerProductSpace NNReal Topology

namespace ThirteenPlanes.ChargeFixed

noncomputable section

variable {N E : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem first_boundary_time {f : ℝ → ℝ} {T r : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn f (Icc 0 T)) (hstart : f 0 < r) (hend : r ≤ f T) :
    ∃ t ∈ Icc 0 T, f t = r ∧ ∀ s ∈ Icc 0 t, f s ≤ r := by
  let S := Icc 0 T ∩ f ⁻¹' Ici r
  have hS : IsCompact S := hc.upperSemicontinuousOn.isCompact_inter_preimage_Ici isCompact_Icc r
  obtain ⟨t,ht,hmin⟩ := hS.exists_isMinOn ⟨T,⟨⟨hT,le_rfl⟩,hend⟩⟩ continuous_id.continuousOn
  have ht0 : t ∈ Icc 0 T := ht.1
  have hft : f t = r := by
    apply le_antisymm _ ht.2
    by_contra! hstrict
    obtain ⟨s,hs,hsr⟩ := intermediate_value_Icc ht0.1 (hc.mono (Icc_subset_Icc_right ht0.2))
      (show r ∈ Icc (f 0) (f t) from ⟨hstart.le,hstrict.le⟩)
    have hS' : s ∈ S := ⟨⟨hs.1,hs.2.trans ht0.2⟩,le_of_eq hsr.symm⟩
    have he : s=t := le_antisymm hs.2 (hmin hS')
    exact (ne_of_gt hstrict) (he ▸ hsr)
  refine ⟨t,ht0,hft,?_⟩
  intro s hs
  by_contra! hstrict
  have hS' : s ∈ S := ⟨⟨hs.1,hs.2.trans ht0.2⟩,hstrict.le⟩
  have he : s=t := le_antisymm hs.2 (hmin hS')
  exact (ne_of_gt hstrict) (he.symm ▸ hft)

private theorem curve_fst {u du : ℝ → E × N} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt u (du t) s t) :
    HasDerivWithinAt (fun t => (u t).1) (du t).1 s t :=
  (ContinuousLinearMap.fst ℝ E N).hasFDerivAt.comp_hasDerivWithinAt t h

private theorem curve_snd {u du : ℝ → E × N} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt u (du t) s t) :
    HasDerivWithinAt (fun t => (u t).2) (du t).2 s t :=
  (ContinuousLinearMap.snd ℝ E N).hasFDerivAt.comp_hasDerivWithinAt t h

private theorem chart_control_on_interval {u du : ℝ → E × N} {K δ T : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (du t) (Ici 0) t)
    (hest : ∀ t ∈ Icc 0 T, ⟪(u t).2,(du t).2⟫ ≤ -δ*‖(u t).2‖^2 ∧ ‖(du t).1‖ ≤ K*‖(u t).2‖)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(u t).2‖ ≤ ‖(u 0).2‖ ∧ ‖(u t).1‖ ≤ ‖(u 0).1‖+K*‖(u 0).2‖/δ := by
  have hn (s : ℝ) (hs : s ∈ Icc 0 T) : ‖(u s).2‖ ≤ ‖(u 0).2‖*Real.exp (-δ*s) :=
    normal_norm_le_exp_on (n := fun t => (u t).2) (dn := fun t => (du t).2)
      (fun w hw => (curve_snd (hu w hw)).mono (fun _ h => h.1)) (fun w hw => (hest w hw).1) hs
  have htangent : ‖(u t).1-(u 0).1‖ ≤ K*‖(u 0).2‖/δ := by
    have hu' : ∀ s ∈ Icc 0 t, HasDerivWithinAt (fun t => (u t).1) (du s).1 (Icc 0 t) s :=
      fun s hs => (curve_fst (hu s ⟨hs.1, hs.2.trans ht.2⟩)).mono (fun _ h => h.1)
    have he : ∀ s ∈ Icc 0 t, ‖(du s).1‖ ≤ (K*‖(u 0).2‖)*Real.exp (-δ*s) := by
      intro s hs
      have hst : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
      exact (hest s hst).2.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hn s hst) hK)
    have h := tangential_exp_displacement hδ ht.1 hu' he
    simp only [mul_zero,Real.exp_zero] at h
    have hb := mul_le_mul_of_nonneg_left (sub_le_self 1 (Real.exp_nonneg (-δ*t)))
      (div_nonneg (mul_nonneg hK (norm_nonneg (u 0).2)) hδ.le)
    exact h.trans (by simpa only [mul_one] using hb)
  constructor
  · exact (hn t ht).trans (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith [ht.1,hδ])))
  · have he : (u t).1 = ((u t).1-(u 0).1)+(u 0).1 := by abel
    calc
      ‖(u t).1‖ ≤ ‖(u t).1-(u 0).1‖+‖(u 0).1‖ := (congrArg norm he).le.trans (norm_add_le _ _)
      _ ≤ _ := by linarith only [htangent]

/-- A forward trajectory subject to local chamber bounds cannot leave the chart ball from a sufficiently close starting point. -/
theorem chamber_stays_in_chart {F : E × N → E × N} {r K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (hest : ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r →
      ⟪y,(F (x,y)).2⟫ ≤ -δ*‖y‖^2 ∧ ‖(F (x,y)).1‖ ≤ K*‖y‖)
    {u : ℝ → E × N} (hc : ContinuousOn u (Ici 0))
    (hu : ∀ t ≥ 0, ‖u t‖ ≤ r → HasDerivWithinAt u (F (u t)) (Ici 0) t)
    (hx0 : ‖(u 0).1‖+K*‖(u 0).2‖/δ < r) (hy0 : ‖(u 0).2‖ < r) :
    ∀ t ≥ 0, ‖u t‖ < r := by
  intro t ht
  by_contra! hbad
  have h0 : ‖u 0‖ < r := by
    rw [Prod.norm_def,max_lt_iff]
    exact ⟨(le_add_of_nonneg_right (div_nonneg (mul_nonneg hK (norm_nonneg _)) hδ.le)).trans_lt hx0,hy0⟩
  obtain ⟨s,hs,he,hsafe⟩ := first_boundary_time ht
    (hc.norm.mono (fun _ hz => hz.1)) h0 hbad
  have H (w : ℝ) (hw : w ∈ Icc 0 s) := hest (u w).1 (u w).2
    ((norm_fst_le (u w)).trans (hsafe w hw)) ((norm_snd_le (u w)).trans (hsafe w hw))
  obtain ⟨hn,hx⟩ := chart_control_on_interval (du := fun w => F (u w)) (T := s) hK hδ
    (fun w hw => hu w hw.1 (hsafe w hw)) H ⟨hs.1,le_rfl⟩
  have hstrict : ‖u s‖ < r := by
    rw [Prod.norm_def,max_lt_iff]
    exact ⟨hx.trans_lt hx0,hn.trans_lt hy0⟩
  exact (ne_of_lt hstrict) he

/-- Under the chart’s coercivity assumptions, an open ball of initial values has global
forward trajectories in the chart, and every such trajectory produced here converges to a
point on the fixed plane inside the chart. -/
theorem chamber_has_local_attracting_ball [CompleteSpace E] [CompleteSpace N]
    {F : E × N → E × N} {r K δ L : ℝ} {LipschitzBound : ℝ≥0}
    (hr : 0 < r) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hF : LipschitzOnWith LipschitzBound F (closedBall 0 r))
    (hL : ∀ p ∈ closedBall 0 r, ‖F p‖ ≤ L)
    (hzero : ∀ x : E, ‖x‖ < r → F (x,0) = 0)
    (hest : ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r →
      ⟪y,(F (x,y)).2⟫ ≤ -δ*‖y‖^2 ∧ ‖(F (x,y)).1‖ ≤ K*‖y‖) :
    ∃ ρ > 0, ∀ p ∈ ball (0 : E × N) ρ, ∃ u : ℝ → E × N, u 0=p ∧
      (∀ t ≥ 0, ‖u t‖ < r ∧ HasDerivWithinAt u (F (u t)) (Ici 0) t) ∧
      ∃ xLimit : E, ‖xLimit‖ < r ∧ F (xLimit,0) = 0 ∧ Tendsto u atTop (𝓝 (xLimit,0)) := by
  let ρ := r/(2+K/δ)
  have hKδ : 0 ≤ K/δ := div_nonneg hK hδ.le
  have hden : 0 < 2+K/δ := by positivity
  have hρ : 0 < ρ := div_pos hr hden
  have hρr : ρ < r := (div_lt_iff₀ hden).mpr (by nlinarith [mul_nonneg hr.le hKδ])
  refine ⟨ρ,hρ,?_⟩
  intro p hp
  have hpρ : ‖p‖ < ρ := by simpa [Metric.mem_ball,dist_zero_right] using hp
  obtain ⟨u,hu0,hu⟩ := exists_forward_of_lipschitz_on_ball hr.le hF hL p
  have hc : ContinuousOn u (Ici 0) := fun t ht => (hu t ht).continuousWithinAt
  have hu_eq (t : ℝ) (ht : 0 ≤ t) (ht' : ‖u t‖ ≤ r) :
      HasDerivWithinAt u (F (u t)) (Ici 0) t := by
    have hmem : u t ∈ closedBall (0 : E × N) r := by simpa [mem_closedBall,dist_zero_right] using ht'
    simpa only [radialClamp_fixed hmem] using hu t ht
  have hxsmall : ‖p.1‖+K*‖p.2‖/δ < r := by
    have hless := (lt_div_iff₀ hden).mp hpρ
    have hprod := mul_le_mul_of_nonneg_left (norm_snd_le p) hKδ
    have hN := norm_fst_le p
    have hn := norm_nonneg p
    have hprod' : K*‖p.2‖/δ ≤ (K/δ)*‖p‖ := by
      convert hprod using 1
      ring
    nlinarith only [hless,hprod',hN,hn]
  have hx0 : ‖(u 0).1‖+K*‖(u 0).2‖/δ < r := by rwa [hu0]
  have hy0 : ‖(u 0).2‖ < r := by rw [hu0]; exact (norm_snd_le p).trans_lt (hpρ.trans hρr)
  have hstay := chamber_stays_in_chart hK hδ hest hc hu_eq hx0 hy0
  have hD (t : ℝ) (ht : 0 ≤ t) := hu_eq t ht (hstay t ht).le
  have hB (t : ℝ) (ht : 0 ≤ t) := hest (u t).1 (u t).2
    ((norm_fst_le _).trans (hstay t ht).le) ((norm_snd_le _).trans (hstay t ht).le)
  obtain ⟨xLimit,hlim⟩ := chamber_trajectory_converges (x := fun t => (u t).1) (n := fun t => (u t).2)
    (dx := fun t => (F (u t)).1) (dn := fun t => (F (u t)).2) hK hδ
    (fun t ht => curve_fst (du := fun s => F (u s)) (hD t ht))
    (fun t ht => curve_snd (du := fun s => F (u s)) (hD t ht))
    (fun t ht => (hB t ht).1) (fun t ht => (hB t ht).2)
  have hbound : ‖xLimit‖ ≤ ‖(u 0).1‖+K*‖(u 0).2‖/δ := by
    have hfst : Tendsto (fun t => (u t).1) atTop (𝓝 xLimit) :=
      (continuous_fst.tendsto (xLimit, (0 : N))).comp hlim
    refine le_of_tendsto_of_tendsto hfst.norm tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (chart_control_on_interval (du := fun t => F (u t)) (T := t) hK hδ
      (fun s hs => hD s hs.1) (fun s hs => hB s hs.1) ⟨ht,le_rfl⟩).2
  exact ⟨u,hu0,fun t ht => ⟨hstay t ht,hD t ht⟩,xLimit,hbound.trans_lt hx0,hzero _ (hbound.trans_lt hx0),hlim⟩


/-- An open set of forward solutions converges to equilibria whenever the straightened vector
field vanishes along the fixed plane and has a uniformly negative normal derivative there at the
base point. The derivative has the required local control, for example for a `C¹` field. -/
theorem chamber_local_attraction_of_negative_normal [CompleteSpace E] [CompleteSpace N]
    (F : E × N → E × N) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hd : ∀ p, ‖p‖ < R → DifferentiableAt ℝ F p)
    (hDnear : ∃ s > 0, ∀ p, ‖p‖ < s → ‖fderiv ℝ F p - fderiv ℝ F 0‖ < δ)
    (hz : ∀ x : E, ‖x‖ < R → F (x,0) = 0)
    (hneg : ∀ y : N, ⟪y,(fderiv ℝ F 0 (0,y)).2⟫ ≤ -(2*δ)*‖y‖^2) :
    ∃ r ∈ Ioo 0 R, ∃ ρ > 0, ∀ p ∈ ball (0 : E × N) ρ, ∃ u : ℝ → E × N, u 0=p ∧
      (∀ t ≥ 0, ‖u t‖ < r ∧ HasDerivWithinAt u (F (u t)) (Ici 0) t) ∧
      ∃ xLimit : E, ‖xLimit‖ < r ∧ F (xLimit,0) = 0 ∧ Tendsto u atTop (𝓝 (xLimit,0)) := by
  obtain ⟨r,hr,K,hF,hB⟩ := local_chamber_speed_bounds F hδ hR hd hDnear hz hneg
  have hz₀ : F (0 : E × N) = 0 := hz 0 (by simpa using hR)
  have hL (p : E × N) (hp : p ∈ closedBall (0 : E × N) r) : ‖F p‖ ≤ (K : ℝ)*r := by
    have hz' : (0 : E × N) ∈ closedBall (0 : E × N) r := by
      simpa [mem_closedBall] using hr.1.le
    have he := hF.dist_le_mul p hp 0 hz'
    rw [hz₀,dist_zero_right,dist_zero_right] at he
    exact he.trans (mul_le_mul_of_nonneg_left (by simpa [mem_closedBall,dist_zero_right] using hp) K.2)
  exact ⟨r,hr,chamber_has_local_attracting_ball hr.1 K.2 hδ hF hL
    (fun x hx => hz x (hx.trans hr.2)) hB⟩

end
end ThirteenPlanes.ChargeFixed
