module

public import ThirteenPlanes.AlbertFlow
public import ThirteenPlanes.Graded.Frames

@[expose] public section

/-! The native positive-mixing flow on the frames constructed by Fourier inversion. -/

namespace ThirteenPlanes.Graded

open Filter Set
open scoped Topology

noncomputable section

/-- Positive mixing on the concrete ternary-graded native Albert pencil. -/
theorem positiveMixing_tendsToRound
    (ε g₀ t₀ : ℝ) (hε : 0 < ε) (hg₀ : g₀ ≠ 0) (ht₀ : 0 < t₀) :
    let initial := (g₀, g₀ * t₀)
    let curve := fun u : ℝ → ℝ × ℝ =>
      IsIntegralCurveOn (fun s => coupling nativeCode.cubicPair (u s))
        (fun _ => oneLoopBeta ε) (Ici 0)
    (∃ u : ℝ → ℝ × ℝ, u 0 = initial ∧ curve u) ∧
    ∀ u : ℝ → ℝ × ℝ, u 0 = initial → curve u →
      let t := fun s => (u s).2 / (u s).1
      (∀ s ∈ Ici (0 : ℝ), (u s).1 ≠ 0 ∧ 0 < t s) ∧
      (t₀ ≤ 1 → MonotoneOn t (Ici 0)) ∧ (1 ≤ t₀ → AntitoneOn t (Ici 0)) ∧
      Tendsto t atTop (𝓝 1) ∧
      Tendsto (fun s => coupling nativeCode.cubicPair (u s)) atTop
        (𝓝 (((if 0 < g₀ then (1 : ℝ) else -1) * 4 * Real.pi * Real.sqrt ε *
          Real.sqrt (1 / 3)) • nativeEqualCubic)) ∧
      Tendsto (fun s => (1 + (t s) ^ 2) / 2) atTop (𝓝 1) :=
  nativeCode.positiveMixing_tendsToRound ε g₀ t₀ hε hg₀ ht₀

/-- The graded native frames realize the constructive flow example from mixing ratio (1/2). -/
theorem exists_positiveMixing_from_half (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℝ → ℝ × ℝ, u 0 = (1, 1 / 2) ∧
      IsIntegralCurveOn (fun s => coupling nativeCode.cubicPair (u s))
        (fun _ => oneLoopBeta ε) (Ici 0) ∧
      Tendsto (fun s => (u s).2 / (u s).1) atTop (𝓝 1) ∧
      Tendsto (fun s => coupling nativeCode.cubicPair (u s)) atTop
        (𝓝 ((4 * Real.pi * Real.sqrt ε * Real.sqrt (1 / 3)) • nativeEqualCubic)) := by
  obtain ⟨⟨u, hu, hc⟩, hall⟩ :=
    positiveMixing_tendsToRound ε 1 (1 / 2) hε (by norm_num) (by norm_num)
  obtain ⟨_, _, _, hratio, hlimit, _⟩ := hall u hu hc
  exact ⟨u, by simpa only [one_mul] using hu, hc, hratio,
    by simpa only [zero_lt_one, ite_true, one_mul] using hlimit⟩

end

end ThirteenPlanes.Graded
