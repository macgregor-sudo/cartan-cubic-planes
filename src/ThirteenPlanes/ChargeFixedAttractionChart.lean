module

public import ThirteenPlanes.ChargeFixedAttractionFlow
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.privateInPublic true

/-! Transport the local attraction theorem through an actual smooth chart. -/

open Filter Set Metric
open scoped ContDiff Topology RealInnerProductSpace

namespace ThirteenPlanes.ChargeFixed

noncomputable section

private theorem derivative_near {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : X → Y} (h : ContDiffAt ℝ 1 F 0)
    {δ : ℝ} (hδ : 0 < δ) : ∃ s > 0, ∀ p, ‖p‖ < s → ‖fderiv ℝ F p-fderiv ℝ F 0‖ < δ := by
  have hc : ContinuousAt (fderiv ℝ F) 0 := h.continuousAt_fderiv one_ne_zero
  obtain ⟨s,hs,hnear⟩ := (Metric.continuousAt_iff.mp hc) δ hδ
  exact ⟨s,hs,fun p hp => by simpa only [dist_eq_norm] using hnear (by simpa only [dist_zero_right] using hp)⟩

variable {N E W : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A smooth fixed-plane parametrization with invertible derivative and a negative normal
linearization gives an open set of initial data that converge to its fixed slice. -/
theorem smooth_chart_has_attracting_neighborhood (B : W → W) (φ : E × N → W)
    (d : (E × N) ≃L[ℝ] W) (hφ : ContDiffAt ℝ 2 φ 0) (hd : HasFDerivAt φ (d : (E × N) →L[ℝ] W) 0)
    (hB : ContDiffAt ℝ 1 B (φ 0))
    (hfixed : ∀ᶠ x in 𝓝 (0 : E), B (φ (x,0)) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hneg : ∀ y : N, ⟪y, (d.symm (fderiv ℝ B (φ 0) (d (0,y)))).2⟫ ≤ -(2*δ)*‖y‖^2) :
    ∃ U : Set W, IsOpen U ∧ φ 0 ∈ U ∧ ∀ p ∈ U, ∃ u : ℝ → W, u 0=p ∧
      (∀ t ≥ 0, HasDerivWithinAt u (B (u t)) (Ici 0) t) ∧
      ∃ xLimit : E, B (φ (xLimit,0)) = 0 ∧ Tendsto u atTop (𝓝 (φ (xLimit,0))) := by
  let F := VectorField.pullback ℝ φ B
  have hi : (fderiv ℝ φ 0).IsInvertible := ⟨d,hd.fderiv.symm⟩
  obtain ⟨M,_,hM,heq,_⟩ := exists_continuousLinearEquiv_fderiv_symm_eq hφ hi
  let A : E × N → W →L[ℝ] E × N := fun x => (M x).symm
  have hM0 : M 0 = d := by
    have he := mem_of_mem_nhds heq
    ext p
    exact congrArg (fun a : (E × N) →L[ℝ] W => a p) (he.trans hd.fderiv)
  have hEq : (fun x => A x (B (φ x))) =ᶠ[𝓝 (0 : E × N)] F :=
    heq.mono fun x hx => (VectorField.pullback_eq_of_fderiv_eq hx B).symm
  have hB0 : B (φ 0) = 0 := mem_of_mem_nhds hfixed
  have hBF : ContDiffAt ℝ 1 (B ∘ φ) 0 := hB.comp 0 (hφ.of_le (by norm_num))
  have hF : ContDiffAt ℝ 1 F 0 := (hM.clm_apply hBF).congr_of_eventuallyEq hEq.symm
  have hFD : fderiv ℝ F 0 = (d.symm : W →L[ℝ] E × N).comp ((fderiv ℝ B (φ 0)).comp d.toContinuousLinearMap) := by
    have hb := (hB.differentiableAt one_ne_zero).hasFDerivAt.comp (0 : E × N) hd
    have hh := (hM.differentiableAt one_ne_zero).hasFDerivAt.clm_apply hb
    have hk := (hh.congr_of_eventuallyEq hEq.symm).fderiv
    rw [Function.comp_apply,hB0,hM0] at hk
    apply ContinuousLinearMap.ext
    intro p
    have hp := congrArg (fun L : (E × N) →L[ℝ] E × N => L p) hk
    simpa only [ContinuousLinearMap.comp_apply,add_apply,
      ContinuousLinearMap.flip_apply,map_zero,add_zero] using hp
  let j := hφ.toOpenPartialHomeomorph φ hd two_ne_zero
  have hsource : (0 : E × N) ∈ j.source := hφ.mem_toOpenPartialHomeomorph_source hd two_ne_zero
  have hfixed' : ∀ᶠ x in 𝓝 (0 : E × N), B (φ (x.1,0)) = 0 :=
    (continuous_fst.tendsto (0 : E × N)).eventually hfixed
  have hnear : ∀ᶠ x in 𝓝 (0 : E × N),
      ContDiffAt ℝ 2 φ x ∧ ContDiffAt ℝ 1 F x ∧ (fderiv ℝ φ x).IsInvertible ∧
        x ∈ j.source ∧ B (φ (x.1,0)) = 0 := by
    filter_upwards [hφ.eventually (by norm_num),hF.eventually (by norm_num),heq,
      j.open_source.mem_nhds hsource,hfixed'] with x hx hf he hs hz
    exact ⟨hx,hf,⟨M x,he⟩,hs,hz⟩
  obtain ⟨R,hR,hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  have hprops (x : E × N) (hx : ‖x‖ < R) := hnear (by simpa only [dist_zero_right] using hx)
  obtain ⟨r,hr,ρ,hρ,hflow⟩ := chamber_local_attraction_of_negative_normal F hδ hR
    (fun x hx => (hprops x hx).2.1.differentiableAt one_ne_zero) (derivative_near hF hδ)
    (fun x hx => by
      have hp : ‖((x : E),(0 : N))‖ < R := by simpa using hx
      have h := (hprops (x,0) hp).2.2.2.2
      simp [F,VectorField.pullback,h])
    (by intro y; rw [hFD]; exact hneg y)
  let ρ' := min ρ R
  have hρ' : 0 < ρ' := lt_min hρ hR
  have hρsource : ball (0 : E × N) ρ' ⊆ j.source := fun p hp =>
    (hprops p ((by simpa only [mem_ball,dist_zero_right] using hp : ‖p‖ < ρ').trans_le
      (min_le_right ρ R))).2.2.2.1
  let U := j '' ball (0 : E × N) ρ'
  refine ⟨U,j.isOpen_image_of_subset_source isOpen_ball hρsource,⟨0,mem_ball_self hρ',rfl⟩,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨u,hu0,hu,xLimit,hxLimit,hzLimit,hlim⟩ := hflow p (ball_subset_ball (min_le_left ρ R) hp)
  let w := φ ∘ u
  refine ⟨w,congrArg φ hu0,?_,xLimit,?_,?_⟩
  · intro t ht
    obtain ⟨hsmall,hderiv⟩ := hu t ht
    have hp' := hprops (u t) (hsmall.trans hr.2)
    have hd' := (hp'.1.differentiableAt two_ne_zero).hasFDerivAt
    have h := HasFDerivAt.comp_hasDerivWithinAt (l := φ) (f := u) t hd' hderiv
    rw [VectorField.fderiv_pullback φ B (u t) hp'.2.2.1] at h
    exact h
  · have hp' : ‖((xLimit : E),(0 : N))‖ < R := by simpa using hxLimit.trans hr.2
    exact (hprops (xLimit,0) hp').2.2.2.2
  · have hp' : ‖((xLimit : E),(0 : N))‖ < R := by simpa using hxLimit.trans hr.2
    exact (hprops (xLimit,0) hp').1.continuousAt.tendsto.comp hlim

end
end ThirteenPlanes.ChargeFixed
