module

public import ThirteenPlanes.PencilFlow.Dynamics.PositiveMixing
public import ThirteenPlanes.NativeFramesPlaneData
public import ThirteenPlanes.Graded.Frames

@[expose] public section

/-! Positive-mixing flow on the actual native Albert pencil of thirteen complementary frames. -/

open Filter Set
open scoped Topology

namespace ThirteenPlanes

noncomputable section

/-- The native trace-free Albert cubic has round strength `1/6`. -/
theorem nativeEqualCubic_isRound : IsRound nativeEqualCubic (1 / 6) := by
  refine ⟨by norm_num, fun x => ?_⟩
  rw [nativeEqualCubic_squareLaw x]
  ring

/-- The planes of an actual tight native code are closed under the centered Jordan product. -/
theorem TightNativeCode.closedPlaneSystem (code : TightNativeCode) :
    IsClosedPlaneSystem nativeEqualCubic code.decomposition := by
  intro i x y hx hy
  change nativeCenteredJordan x y ∈ nativeFramePlane (code.point i)
  exact nativeFramePlane_closed (code.frame i) hx hy

/-- The flow pencil uses exactly the cubic pair assembled from the actual frame planes. -/
theorem TightNativeCode.planePencil_eq_cubicPair (code : TightNativeCode) :
    planePencil nativeEqualCubic code.decomposition = code.cubicPair := rfl

/-- The flow parameter `(N-2)/12` of the trace-free native Albert space is two. -/
theorem nativeAlbert_pencilLambda : PencilFlow.Statements.pencilLambda NativeTraceless = 2 := by
  norm_num [PencilFlow.Statements.pencilLambda, nativeTraceless_finrank]

/-- Positive mixing on any native tight-code pencil has the full forward limit at the actual
round member. The coefficient and field solutions are in physical time. -/
theorem TightNativeCode.positiveMixing_tendsToRound (code : TightNativeCode)
    (ε g₀ t₀ : ℝ) (hε : 0 < ε) (hg₀ : g₀ ≠ 0) (ht₀ : 0 < t₀) :
    let initial := (g₀, g₀ * t₀)
    let curve := fun u : ℝ → ℝ × ℝ =>
      IsIntegralCurveOn (fun s => coupling code.cubicPair (u s))
        (fun _ => oneLoopBeta ε) (Ici 0)
    (∃ u : ℝ → ℝ × ℝ, u 0 = initial ∧ curve u) ∧
    ∀ u : ℝ → ℝ × ℝ, u 0 = initial → curve u →
      let t := fun s => (u s).2 / (u s).1
      (∀ s ∈ Ici (0 : ℝ), (u s).1 ≠ 0 ∧ 0 < t s) ∧
      (t₀ ≤ 1 → MonotoneOn t (Ici 0)) ∧ (1 ≤ t₀ → AntitoneOn t (Ici 0)) ∧
      Tendsto t atTop (𝓝 1) ∧
      Tendsto (fun s => coupling code.cubicPair (u s)) atTop
        (𝓝 (((if 0 < g₀ then (1 : ℝ) else -1) * 4 * Real.pi * Real.sqrt ε *
          Real.sqrt (1 / 3)) • nativeEqualCubic)) ∧
      Tendsto (fun s => (1 + (t s) ^ 2) / 2) atTop (𝓝 1) := by
  have h := PencilFlow.Proofs.positiveMixing_tendsToRound NativeTraceless
    (m := 13) (by decide) nativeEqualCubic (1 / 6) code.decomposition
    nativeEqualCubic_isRound code.closedPlaneSystem ε g₀ t₀ hε hg₀ ht₀
  have hscale : (2 / ((1 / 6 : ℝ) * ((26 : ℝ) + 10))) = 1 / 3 := by norm_num
  simpa only [code.planePencil_eq_cubicPair, nativeTraceless_finrank, Nat.cast_ofNat,
    code.interaction_one, hscale] using h

/-- The ternary-graded frames realize the native flow from mixing ratio `1/2`. -/
theorem exists_nativeAlbert_positiveMixing (ε : ℝ) (hε : 0 < ε) :
    ∃ (code : TightNativeCode) (u : ℝ → ℝ × ℝ),
      u 0 = (1, 1 / 2) ∧
      IsIntegralCurveOn (fun s => coupling code.cubicPair (u s))
        (fun _ => oneLoopBeta ε) (Ici 0) ∧
      Tendsto (fun s => (u s).2 / (u s).1) atTop (𝓝 1) ∧
      Tendsto (fun s => coupling code.cubicPair (u s)) atTop
        (𝓝 ((4 * Real.pi * Real.sqrt ε * Real.sqrt (1 / 3)) • nativeEqualCubic)) := by
  let code := Graded.nativeCode
  have hf := code.positiveMixing_tendsToRound ε 1 (1 / 2) hε (by norm_num) (by norm_num)
  obtain ⟨⟨u, hu, hc⟩, hall⟩ := hf
  obtain ⟨_, _, _, hratio, hlimit, _⟩ := hall u hu hc
  refine ⟨code, u, by simpa only [one_mul] using hu, hc, hratio, ?_⟩
  simpa only [zero_lt_one, ite_true, one_mul] using hlimit

end

end ThirteenPlanes
