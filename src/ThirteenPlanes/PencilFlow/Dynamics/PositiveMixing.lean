module

public import ThirteenPlanes.PencilFlow.Dynamics.Physical

@[expose] public section

/-! Positive mixing: along the normalized planar field, a solution with positive initial ratio keeps a
positive ratio, moves monotonically toward `1` and converges to the equal-strength point. The
physical statement follows by the rescaling `w = √(6c) u`. -/

open Filter Set
open scoped Topology

namespace ThirteenPlanes.PencilFlow.Dynamics

noncomputable section

open Statements ThirteenPlanes

variable {lam ε : ℝ} {w : ℝ → ℝ × ℝ}

/-- The positive sector of the normalized coefficient field for every `lam > 0`. -/
theorem positive_sector (hlam : 0 < lam) (hε : 0 < ε)
    (hw : IsIntegralCurveOn w (fun _ ↦ familyField lam ε) (Ici 0))
    (ha0 : (w 0).1 ≠ 0) (ht0 : 0 < (w 0).2 / (w 0).1) :
    (∀ s ∈ Ici (0 : ℝ), (w s).1 ≠ 0 ∧ 0 < (w s).2 / (w s).1) ∧
    ((w 0).2 / (w 0).1 ≤ 1 → MonotoneOn (fun s => (w s).2 / (w s).1) (Ici 0)) ∧
    (1 ≤ (w 0).2 / (w 0).1 → AntitoneOn (fun s => (w s).2 / (w s).1) (Ici 0)) ∧
    Tendsto (fun s => (w s).2 / (w s).1) atTop (𝓝 1) ∧
    (0 < (w 0).2 → Tendsto w atTop
        (𝓝 (equalStrengthLevel lam ε, equalStrengthLevel lam ε))) ∧
    ((w 0).2 < 0 → Tendsto w atTop
        (𝓝 (-equalStrengthLevel lam ε, -equalStrengthLevel lam ε))) := by
  have hb0 : (w 0).2 ≠ 0 := by intro h; rw [h, zero_div] at ht0; exact lt_irrefl 0 ht0
  have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hw) hb0
  set t0 := (w 0).2 / (w 0).1 with ht0_def
  have hq : 0 < (w 0).2 * (lam * (w 0).2 + (w 0).1) := by
    rw [sectorQ_eq_chart lam ha0]
    have : 0 < (w 0).1 ^ 2 := by positivity
    have : 0 < lam * t0 + 1 := by positivity
    positivity
  set v : ℝ → ℝ := fun s ↦ (w s).1 / (w s).2 with hv_def
  have hv' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt v
      ((w s).2 ^ 2 * (1 - v s) * (v s + lam) / flowScale) (Ici 0) s := fun s hs ↦
    familyField_hasDerivWithinAt_inverseRatio (hb s hs) (solution_fst hw s hs)
      (solution_snd hw s hs)
  have hq' := pos_of_pos_mul (sectorQ_eq_pos_mul hlam.ne' hw) hq
  have hlamv : ∀ s, 0 ≤ s → 0 < v s + lam := by
    intro s hs
    have h1 := hq' s hs
    have hbs := hb s hs
    have e : (w s).2 * (lam * (w s).2 + (w s).1) = (w s).2 ^ 2 * (v s + lam) := by
      simp only [v]; field_simp; ring
    rw [e] at h1
    by_contra hneg
    rw [not_lt] at hneg
    linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w s).2) hneg]
  have hpe : ∀ s, (w s).2 ≠ 0 →
      (w s).2 * ((w s).2 - (w s).1) = (w s).2 ^ 2 * (1 - v s) := fun s hbs ↦ by
    simp only [v]; field_simp
  have hpm := sectorP_eq_pos_mul hw
  have hp0 : (w 0).2 * ((w 0).2 - (w 0).1) = (w 0).1 ^ 2 * (t0 * (t0 - 1)) := by
    simp only [t0]; field_simp
  have hv0 : v 0 = t0⁻¹ := by simp only [v, t0, inv_div]
  have hv0pos : 0 < v 0 := by rw [hv0]; positivity
  -- `t0 ≤ 1` gives `v ≥ 1`; `1 ≤ t0` gives `v ≤ 1`
  have hge : t0 ≤ 1 → ∀ s, 0 ≤ s → 1 ≤ v s := by
    intro ht s hs
    have hle0 : (w 0).2 * ((w 0).2 - (w 0).1) ≤ 0 := by
      rw [hp0]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (mul_nonpos_of_nonneg_of_nonpos ht0.le (by linarith))
    obtain ⟨k, hk, e⟩ := hpm s hs
    have h1 : (w s).2 * ((w s).2 - (w s).1) ≤ 0 := by
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos hk.le hle0
    rw [hpe s (hb s hs)] at h1
    have : 0 < (w s).2 ^ 2 := by have := hb s hs; positivity
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hle : 1 ≤ t0 → ∀ s, 0 ≤ s → v s ≤ 1 := by
    intro ht s hs
    have hle0 : 0 ≤ (w 0).2 * ((w 0).2 - (w 0).1) := by
      rw [hp0]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg ht0.le (by linarith))
    obtain ⟨k, hk, e⟩ := hpm s hs
    have h1 : 0 ≤ (w s).2 * ((w s).2 - (w s).1) := by
      rw [e]; exact mul_nonneg hk.le hle0
    rw [hpe s (hb s hs)] at h1
    have : 0 < (w s).2 ^ 2 := by have := hb s hs; positivity
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hmono : 1 ≤ t0 → MonotoneOn v (Ici 0) := fun ht ↦
    monotoneOn_Ici_of_deriv_nonneg hv' fun s hs ↦ by
      apply div_nonneg _ flowScale_pos.le
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith [hle ht s hs])) (hlamv s hs).le
  have hanti : t0 ≤ 1 → AntitoneOn v (Ici 0) := fun ht ↦ by
    have := monotoneOn_Ici_of_deriv_nonneg (y := fun s ↦ -v s)
      (fun s hs ↦ (hv' s hs).neg) fun s hs ↦ by
        rw [neg_nonneg]
        apply div_nonpos_of_nonpos_of_nonneg _ flowScale_pos.le
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hge ht s hs]))
          (hlamv s hs).le
    intro a ha b hb hab
    have := this ha hb hab
    simpa using this
  have hvpos : ∀ s, 0 ≤ s → 0 < v s := by
    intro s hs
    rcases le_total t0 1 with ht | ht
    · linarith [hge ht s hs]
    · exact lt_of_lt_of_le hv0pos (hmono ht (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs)
  have hratio : ∀ s, (w s).2 / (w s).1 = (v s)⁻¹ := fun s ↦ by simp only [v, inv_div]
  refine ⟨fun s hs ↦ ⟨?_, ?_⟩, fun ht ↦ ?_, fun ht ↦ ?_, ?_,
    (tendsto_equalStrength_point' hlam hε hw hq).1, (tendsto_equalStrength_point' hlam hε hw hq).2⟩
  · have h1 := hvpos s hs
    simp only [v] at h1
    intro h0; rw [h0, zero_div] at h1; exact lt_irrefl 0 h1
  · rw [hratio]; exact inv_pos.mpr (hvpos s hs)
  · intro a ha b hb hab
    simp only [hratio]
    exact inv_anti₀ (hvpos b hb) (hanti ht ha hb hab)
  · intro a ha b hb hab
    simp only [hratio]
    exact inv_anti₀ (hvpos a ha) (hmono ht ha hb hab)
  · have := (tendsto_inverseRatio_one' hlam hε hw hq).inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr' (Eventually.of_forall fun s ↦ ?_)
    exact (hratio s).symm

/-- The equal-strength level in physical units. -/
theorem physical_level {c : ℝ} (hc : 0 < c) (hε : 0 < ε) (n : ℝ) (hn : 0 < n + 10) :
    (Real.sqrt (6 * c))⁻¹ * equalStrengthLevel ((n - 2) / 12) ε =
      4 * Real.pi * Real.sqrt ε * Real.sqrt (2 / (c * (n + 10))) := by
  have hK := flowScale_pos
  have h1 : 0 ≤ flowScale * ε / (1 + (n - 2) / 12) := by
    have : 0 < 1 + (n - 2) / 12 := by linarith
    positivity
  have h2 : 0 ≤ 2 / (c * (n + 10)) := by positivity
  rw [← sq_eq_sq₀ (by unfold equalStrengthLevel; positivity) (by positivity)]
  simp only [mul_pow, inv_pow, equalStrengthLevel]
  rw [Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sq_sqrt hε.le, Real.sq_sqrt (by positivity)]
  rw [show 1 + (n - 2) / 12 = (n + 10) / 12 by ring]
  have hn' : n + 10 ≠ 0 := hn.ne'
  unfold flowScale
  field_simp
  ring

end

end ThirteenPlanes.PencilFlow.Dynamics

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements Dynamics

/-- The one-loop pencil flow, global existence, monotone ratio and the round limit for positive
mixing. -/
theorem positiveMixing_tendsToRound (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.PositiveMixingLimit V := by
  intro m hm h c planes hround hclosed ε g₀ t₀ hε hg₀ ht₀
  dsimp only
  have hc := hround.positive
  have hlam := pencilLambda_pos hm planes
  set P := planePencil h planes
  set σ := Real.sqrt (6 * c) with hσ_def
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσ : σ ^ 2 = 6 * c := Real.sq_sqrt (by positivity)
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw0, hw⟩ := exists_forward_solution hlam ε (σ • (g₀, g₀ * t₀))
    refine ⟨fun s => σ⁻¹ • w s, by show σ⁻¹ • w 0 = _; rw [hw0, inv_smul_smul₀ hσ0.ne'],
      fun s hs => ?_⟩
    exact tensor_deriv_of_coeff hround hclosed ε (integralCurve_unscale hσ hσ0.ne' hw s hs)
  intro u hu0 hu
  have hu' : IsIntegralCurveOn u (fun _ => physicalCoefficientField c (pencilLambda V) ε)
      (Ici 0) := fun s hs => coeff_deriv_of_tensor hm hround hclosed ε (hu s hs)
  have hw := integralCurve_scale hσ hu'
  set w := fun s => σ • u s with hw_def
  have hw0 : w 0 = (σ * g₀, σ * (g₀ * t₀)) := by simp [w, hu0]
  have hratio : ∀ s, (w s).2 / (w s).1 = (u s).2 / (u s).1 := fun s => by
    simp only [w, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact mul_div_mul_left _ _ hσ0.ne'
  have ha0 : (w 0).1 ≠ 0 := by rw [hw0]; exact mul_ne_zero hσ0.ne' hg₀
  have ht0 : (w 0).2 / (w 0).1 = t₀ := by rw [hratio, hu0]; field_simp
  obtain ⟨hpos, hmono, hanti, hlim, hpt, hnt⟩ :=
    positive_sector hlam hε hw ha0 (by rw [ht0]; exact ht₀)
  have hu0r : (u 0).2 / (u 0).1 = t₀ := by rw [← hratio, ht0]
  simp only [hratio] at hpos hmono hanti hlim
  simp only [hu0r] at hmono hanti
  have hlimit : ∀ L : ℝ, Tendsto w atTop (𝓝 (L, L)) →
      Tendsto (fun s => coupling P (u s)) atTop (𝓝 ((σ⁻¹ * L) • interactionCubic P 1)) := by
    intro L hL
    have hu_eq : (fun s => u s) = fun s => σ⁻¹ • w s := by
      funext s; simp [w, inv_smul_smul₀ hσ0.ne']
    have h1 := ((coupling P).continuous_of_finiteDimensional.tendsto _).comp (hL.const_smul σ⁻¹)
    rw [← coupling_same]
    refine h1.congr fun s => ?_
    simp [w, inv_smul_smul₀ hσ0.ne']
  have hn : (0 : ℝ) < (Module.finrank ℝ V : ℝ) + 10 := by positivity
  have hlev := physical_level hc hε (Module.finrank ℝ V : ℝ) hn
  refine ⟨fun s hs => ⟨?_, (hpos s hs).2⟩, hmono, hanti, hlim, ?_, ?_⟩
  · have := (hpos s hs).1
    simp only [w, Prod.smul_fst, smul_eq_mul] at this
    exact right_ne_zero_of_mul this
  · split_ifs with hg
    · have hb : 0 < (w 0).2 := by rw [hw0]; positivity
      have := hlimit _ (hpt hb)
      convert this using 2
      unfold pencilLambda at *
      rw [hlev]; ring_nf
    · have hg' : g₀ < 0 := lt_of_le_of_ne (not_lt.mp hg) hg₀
      have hb : (w 0).2 < 0 := by
        rw [hw0]; exact mul_neg_of_pos_of_neg hσ0 (mul_neg_of_neg_of_pos hg' ht₀)
      have := hlimit _ (hnt hb)
      convert this using 2
      unfold pencilLambda at *
      rw [mul_neg, hlev]; ring_nf
  · have := ((hlim.pow 2).const_add 1).div_const 2
    norm_num at this ⊢
    exact this

end ThirteenPlanes.PencilFlow.Proofs
