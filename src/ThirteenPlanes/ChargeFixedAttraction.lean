module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

set_option backward.privateInPublic true

/-! Normal decay and tangential displacement for the local fixed-manifold argument. -/

open scoped RealInnerProductSpace Interval Topology NNReal
open Set Filter MeasureTheory

namespace ThirteenPlanes.ChargeFixed

noncomputable section

variable {N E : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasDerivAt_norm_sq_real {f : ℝ → N} {d : N} {t : ℝ} (h : HasDerivAt f d t) :
    HasDerivAt (fun s => ‖f s‖^2) (2*⟪f t,d⟫) t := by
  convert h.inner ℝ h using 1
  · funext s
    exact (real_inner_self_eq_norm_sq (f s)).symm
  · rw [real_inner_comm d, two_mul]

private theorem hasDerivAt_exp_mul (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (a*s)) (a*Real.exp (a*t)) t := by
  convert (Real.hasDerivAt_exp (a*t)).comp t ((hasDerivAt_id t).const_mul a) using 1
  · rfl
  · simp [mul_comm]

/-- A coercive normal velocity gives exact exponential decay on each closed time interval. -/
theorem normal_norm_le_exp_on {n dn : ℝ → N} {T δ : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt n (dn t) (Icc 0 T) t)
    (hcoerce : ∀ t ∈ Icc 0 T, ⟪n t,dn t⟫ ≤ -δ*‖n t‖^2)
    {t : ℝ} (ht : t ∈ Icc 0 T) : ‖n t‖ ≤ ‖n 0‖ * Real.exp (-δ*t) := by
  let w : ℝ → ℝ := fun s => Real.exp (2*δ*s)*‖n s‖^2
  have hw (s : ℝ) (hs : s ∈ Ioo 0 T) :
      HasDerivAt w (Real.exp (2*δ*s)*(2*δ*‖n s‖^2+2*⟪n s,dn s⟫)) s := by
    have hd' := (hd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    convert (hasDerivAt_exp_mul (2*δ) s).mul (hasDerivAt_norm_sq_real hd') using 1
    ring
  have hcn : ContinuousOn n (Icc 0 T) := fun s hs => (hd s hs).continuousWithinAt
  have ha : AntitoneOn w (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact (by fun_prop : ContinuousOn (fun s : ℝ => Real.exp (2*δ*s)) (Icc 0 T)).mul (hcn.norm.pow 2)
    · rw [interior_Icc]
      exact fun s hs => (hw s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hw s hs).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      nlinarith only [hcoerce s (Ioo_subset_Icc_self hs)]
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl,ht.1.trans ht.2⟩
  have hb := ha hz ht ht.1
  change Real.exp (2*δ*t)*‖n t‖^2 ≤ Real.exp (2*δ*0)*‖n 0‖^2 at hb
  simp only [mul_zero,Real.exp_zero,one_mul] at hb
  have hc := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-2*δ*t))
  rw [← mul_assoc,← Real.exp_add,show -2*δ*t+2*δ*t=0 by ring,Real.exp_zero,one_mul] at hc
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))).mp
  rw [mul_pow,show Real.exp (-δ*t)^2 = Real.exp (-2*δ*t) by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring]
  simpa only [mul_comm] using hc

/-- Tangential displacement is bounded by the integral of its exponentially decaying speed. -/
theorem tangential_exp_displacement {x dx : ℝ → E} {K δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt x (dx t) (Icc a b) t)
    (hbound : ∀ t ∈ Icc a b, ‖dx t‖ ≤ K*Real.exp (-δ*t)) :
    ‖x b-x a‖ ≤ (K/δ)*(Real.exp (-δ*a)-Real.exp (-δ*b)) := by
  have hc : Continuous (fun t : ℝ => K*Real.exp (-δ*t)) := by fun_prop
  have hi : IntervalIntegrable (fun t : ℝ => K*Real.exp (-δ*t)) volume a b := hc.intervalIntegrable a b
  have hdist := norm_sub_le_integral_of_norm_deriv_le_of_le hab
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => ((hd t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall fun t ht => by
      have hs : t ∈ Icc a b := Ioo_subset_Icc_self ht
      rw [((hd t hs).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      exact hbound t hs) hi
  have hdF (t : ℝ) : HasDerivAt (fun s : ℝ => -(K/δ)*Real.exp (-δ*s)) (K*Real.exp (-δ*t)) t := by
    convert (hasDerivAt_exp_mul (-δ) t).const_mul (-(K/δ)) using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hdF t) hi] at hdist
  convert hdist using 1
  ring

private theorem exp_neg_mul_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => Real.exp (-δ*t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hδ)).mpr tendsto_id)

/-- A forward trajectory with uniform normal coercivity and tangential speed control
converges to a point on the plane of fixed states. -/
theorem chamber_trajectory_converges [CompleteSpace E] {x dx : ℝ → E} {n dn : ℝ → N} {K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hxd : ∀ t ≥ 0, HasDerivWithinAt x (dx t) (Ici 0) t)
    (hnd : ∀ t ≥ 0, HasDerivWithinAt n (dn t) (Ici 0) t)
    (hcoerce : ∀ t ≥ 0, ⟪n t,dn t⟫ ≤ -δ*‖n t‖^2)
    (hbound : ∀ t ≥ 0, ‖dx t‖ ≤ K*‖n t‖) :
    ∃ xLimit, Tendsto (fun t : ℝ => (x t,n t)) atTop (𝓝 (xLimit,0)) := by
  have hnorm t (ht : 0 ≤ t) : ‖n t‖ ≤ ‖n 0‖*Real.exp (-δ*t) :=
    normal_norm_le_exp_on (T := t)
      (fun s hs => (hnd s hs.1).mono (fun _ ht => ht.1)) (fun s hs => hcoerce s hs.1) ⟨ht,le_rfl⟩
  have hn : Tendsto n atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hnorm t ht
    · simpa only [mul_zero] using tendsto_const_nhds.mul (exp_neg_mul_atTop hδ)
  let C := K*‖n 0‖/δ
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hK (norm_nonneg _)) hδ.le
  have htail {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : dist (x b) (x a) ≤ C*Real.exp (-δ*a) := by
    have h := tangential_exp_displacement (K := K*‖n 0‖) hδ hab
      (fun s hs => (hxd s (ha.trans hs.1)).mono (fun _ ht => ha.trans ht.1)) (fun s hs => by
        have her := mul_le_mul_of_nonneg_left (hnorm s (ha.trans hs.1)) hK
        exact (hbound s (ha.trans hs.1)).trans (by simpa only [mul_assoc] using her))
    rw [dist_eq_norm]
    calc
      _ ≤ C*(Real.exp (-δ*a)-Real.exp (-δ*b)) := h
      _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_nonneg _)) hC
  have hsmall : Tendsto (fun t : ℝ => C*Real.exp (-δ*t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (exp_neg_mul_atTop hδ)
  have hc : Cauchy (Filter.map x atTop) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance,?_⟩
    intro ε hε
    obtain ⟨T,hT⟩ := Metric.tendsto_atTop.mp hsmall ε hε
    let S := max T 0
    refine ⟨x '' Ici S,?_,?_⟩
    · apply Filter.mem_map.mpr
      filter_upwards [eventually_ge_atTop S] with t ht
      exact ⟨t,ht,rfl⟩
    · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
      have haa : 0 ≤ a := (le_max_right _ _).trans ha
      have hbb : 0 ≤ b := (le_max_right _ _).trans hb
      have hsa : C*Real.exp (-δ*a) < ε := by
        simpa [Real.dist_eq,abs_of_nonneg hC] using
          hT a ((le_max_left _ _).trans ha)
      have hsb : C*Real.exp (-δ*b) < ε := by
        simpa [Real.dist_eq,abs_of_nonneg hC] using
          hT b ((le_max_left _ _).trans hb)
      rcases le_total a b with hab|hba
      · rw [dist_comm]
        exact (htail haa hab).trans_lt hsa
      · exact (htail hbb hba).trans_lt hsb
  obtain ⟨xLimit,hxLimit⟩ := cauchy_map_iff_exists_tendsto.mp hc
  exact ⟨xLimit,hxLimit.prodMk_nhds hn⟩

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- A negative normal derivative at the base point gives uniform normal coercivity and
linear tangential speed control on a smaller product box. -/
theorem local_chamber_speed_bounds (F : E × N → E × N) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hd : ∀ p, ‖p‖ < R → DifferentiableAt ℝ F p)
    (hDnear : ∃ s > 0, ∀ p, ‖p‖ < s → ‖fderiv ℝ F p - fderiv ℝ F 0‖ < δ)
    (hz : ∀ x : E, ‖x‖ < R → F (x,0) = 0)
    (hneg : ∀ y : N, ⟪y, (fderiv ℝ F 0 (0,y)).2⟫ ≤ -(2*δ)*‖y‖^2) :
    ∃ r ∈ Ioo 0 R, ∃ K : ℝ≥0, LipschitzOnWith K F (Metric.closedBall 0 r) ∧
      ∀ (x : E) (y : N), ‖x‖ ≤ r → ‖y‖ ≤ r →
        ⟪y,(F (x,y)).2⟫ ≤ -δ*‖y‖^2 ∧ ‖(F (x,y)).1‖ ≤ K*‖y‖ := by
  let A := fderiv ℝ F 0
  obtain ⟨s,hs,hnear⟩ := hDnear
  let r := min (s/2) (R/2)
  have hr : 0 < r := lt_min (half_pos hs) (half_pos hR)
  have hrs : r < s := (min_le_left _ _).trans_lt (half_lt_self hs)
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  let K : ℝ≥0 := ⟨‖A‖+δ,by positivity⟩
  let S := Metric.closedBall (0 : E × N) r
  have hB (w : E × N) (hw : w ∈ S) : ‖fderiv ℝ F w-A‖ ≤ δ := by
    have hm : ‖w‖ ≤ r := by simpa [S,Metric.mem_closedBall,dist_zero_right] using hw
    exact (hnear w (hm.trans_lt hrs)).le
  have hds (w : E × N) (hw : w ∈ S) : DifferentiableAt ℝ F w := by
    have hw' : ‖w‖ ≤ r := by simpa [S,Metric.mem_closedBall,dist_zero_right] using hw
    exact hd w (hw'.trans_lt hrR)
  refine ⟨r,⟨hr,hrR⟩,K,?_,?_⟩
  · apply Convex.lipschitzOnWith_of_nnNorm_fderiv_le hds _ (convex_closedBall (0 : E × N) r)
    intro w hw
    change ‖fderiv ℝ F w‖ ≤ ‖A‖+δ
    calc
      ‖fderiv ℝ F w‖ = ‖(fderiv ℝ F w-A)+A‖ := by rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ F w-A‖+‖A‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ _ := by linarith only [hB w hw]
  intro x y hx hy
  let p : E × N := (x,y)
  let q : E × N := (x,0)
  have hp : p ∈ S := by simp [S,p,Metric.mem_closedBall,hx,hy]
  have hq : q ∈ S := by simp [S,q,Metric.mem_closedBall,hx]
  let g : E × N → E × N := fun w => F w-A w
  have hD (w : E × N) (hw : w ∈ S) :
      HasFDerivWithinAt g (fderiv ℝ F w-A) S w := by
    exact ((hds w hw).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt
  have hLip := (convex_closedBall (0 : E × N) r).norm_image_sub_le_of_norm_hasFDerivWithin_le hD hB hq hp
  have hpq : p-q = (0,y) := by simp [p,q]
  have hnorm : ‖p-q‖ = ‖y‖ := by rw [hpq,Prod.norm_def]; simp
  have hFq : F q = 0 := hz x (hx.trans_lt hrR)
  have hrem : ‖F p - A (0,y)‖ ≤ δ*‖y‖ := by
    have he : g p-g q = F p-A (0,y) := by
      simp only [g,hFq,zero_sub,sub_neg_eq_add]
      rw [← hpq,map_sub]
      abel
    rwa [he,hnorm] at hLip
  have herr : ‖(F p).2-(A (0,y)).2‖ ≤ δ*‖y‖ :=
    (norm_snd_le (F p-A (0,y))).trans hrem
  have hinner : ⟪y,(F p).2-(A (0,y)).2⟫ ≤ ‖y‖*(δ*‖y‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left herr (norm_nonneg _))
  constructor
  · rw [inner_sub_right] at hinner
    change ⟪y,(F p).2⟫ ≤ _
    nlinarith only [hneg y,hinner]
  · change ‖(F p).1‖ ≤ (‖A‖+δ)*‖y‖
    have hA : ‖A (0,y)‖ ≤ ‖A‖*‖y‖ := by
      have h := A.le_opNorm ((0 : E),y)
      simpa [Prod.norm_def] using h
    have he : F p = (F p-A (0,y))+A (0,y) := by abel
    calc
      _ ≤ ‖F p‖ := norm_fst_le _
      _ ≤ ‖F p-A (0,y)‖+‖A (0,y)‖ := (congrArg norm he).le.trans (norm_add_le _ _)
      _ ≤ _ := by linarith only [hrem,hA]

end
end ThirteenPlanes.ChargeFixed
