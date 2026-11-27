/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.NativeFramesCarrier
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The planes of an arbitrary tight 39-point code in the native compact Albert algebra.
The labelled code data are the frame formulation in Appendix `app:further-support`. -/

noncomputable section

namespace ThirteenPlanes

/-- Thirteen native Jordan frames whose cross-frame point overlaps are (1/3). -/
structure TightNativeCode where
  point : Fin 13 → Fin 3 → Glennie.Albert
  frame : ∀ f, Glennie.Frame (point f)
  overlap : ∀ {f g}, f ≠ g → ∀ a b, Glennie.inner (point f a) (point g b) = 1 / 3

def nativeFrameSynthesis (p : Fin 3 → Glennie.Albert) :
    (Fin 3 → ℝ) →ₗ[ℝ] Glennie.Albert where
  toFun u := ∑ b, u b • p b
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum, mul_smul]

theorem nativeFrameSynthesis_trace {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (u : Fin 3 → ℝ) : Glennie.trace (nativeFrameSynthesis p u) = ∑ b, u b := by
  change Glennie.traceLinear (∑ b, u b • p b) = _
  simp [hp.trace_one]

theorem nativeFrameSynthesis_const {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (r : ℝ) : nativeFrameSynthesis p (fun _ => r) = r • (1 : Glennie.Albert) := by
  change (∑ b, r • p b) = _
  rw [← Finset.smul_sum, Fin.sum_univ_three, hp.sum_unit]

theorem nativeFrame_jordan {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (a b : Fin 3) :
    Glennie.jordan (p a) (p b) = if a = b then p a else 0 := by
  by_cases h : a = b
  · subst b
    simpa using hp.idempotent a
  · rw [ite_eq_right h, hp.orthogonal a b h]

theorem nativeFrame_gram {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (a b : Fin 3) :
    Glennie.inner (p a) (p b) = if a = b then 1 else 0 := by
  simp [Glennie.inner, nativeFrame_jordan hp, apply_ite, hp.trace_one]

theorem TightNativeCode.points_injective (c : TightNativeCode) :
    Function.Injective (fun ab : Fin 13 × Fin 3 => c.point ab.1 ab.2) := by
  rintro ⟨f, a⟩ ⟨g, b⟩ heq
  change c.point f a = c.point g b at heq
  have hself : Glennie.inner (c.point f a) (c.point f a) = 1 := by simp [nativeFrame_gram (c.frame f)]
  have hfg : f = g := by
    by_contra hn
    have hcross := c.overlap hn a b
    rw [← heq, hself] at hcross
    norm_num at hcross
  subst g
  have hab : a = b := by
    by_contra hn
    have hcross := nativeFrame_gram (c.frame f) a b
    rw [← heq, hself, ite_eq_right hn] at hcross
    norm_num at hcross
  subst b
  rfl

theorem nativeFrameSynthesis_inner (p : Fin 3 → Glennie.Albert) (u : Fin 3 → ℝ)
    (x : Glennie.Albert) :
    Glennie.inner (nativeFrameSynthesis p u) x = ∑ b, u b * Glennie.inner (p b) x := by
  change inner ℝ (∑ b, u b • p b) x = _
  simp only [sum_inner, real_inner_smul_left, Glennie.hilbert_inner_eq_native]

theorem nativeFrame_inner_synthesis (p : Fin 3 → Glennie.Albert) (x : Glennie.Albert)
    (u : Fin 3 → ℝ) :
    Glennie.inner x (nativeFrameSynthesis p u) = ∑ b, u b * Glennie.inner x (p b) := by
  rw [Glennie.inner_comm x, nativeFrameSynthesis_inner]
  simp only [Glennie.inner_comm (p _) x]

theorem nativeFrame_analysis_synthesis {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (u : Fin 3 → ℝ) (a : Fin 3) :
    Glennie.inner (p a) (nativeFrameSynthesis p u) = u a := by
  rw [nativeFrame_inner_synthesis]
  simp [nativeFrame_gram hp, mul_ite]

theorem nativeFrameSynthesis_jordan {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (u v : Fin 3 → ℝ) :
    Glennie.jordan (nativeFrameSynthesis p u) (nativeFrameSynthesis p v) =
      nativeFrameSynthesis p (fun b => u b * v b) := by
  change Glennie.jordan (∑ b, u b • p b) (∑ b, v b • p b) = ∑ b, (u b * v b) • p b
  simp only [← Glennie.jordanLinear_apply, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.smul_sum]
  simp only [Glennie.jordanLinear_apply, nativeFrame_jordan hp]
  rw [Finset.sum_eq_single b]
  · simp [smul_smul, mul_comm]
  · intro a _ h
    simp [h]
  · simp

theorem nativeFrameSynthesis_centered {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (u : Fin 3 → ℝ) :
    Glennie.traceless (nativeFrameSynthesis p u) =
      nativeFrameSynthesis p (fun b => u b - (∑ c, u c) / 3) := by
  have hu : (fun b => u b - (∑ c, u c) / 3) = u - (fun _ => (∑ c, u c) / 3) := rfl
  rw [hu, Glennie.traceless, nativeFrameSynthesis_trace hp, map_sub, nativeFrameSynthesis_const hp]

def nativeFrameEntries : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun u := ![u 0, u 1, -(u 0 + u 1)]
  map_add' u v := by
    funext b
    fin_cases b <;> simp [add_assoc, add_comm, add_left_comm]
  map_smul' r u := by
    funext b
    fin_cases b <;> simp [Pi.smul_apply, smul_eq_mul, mul_add]

theorem nativeFrameEntries_sum (u : Fin 2 → ℝ) : ∑ b, nativeFrameEntries u b = 0 := by
  change ∑ b, (![u 0, u 1, -(u 0 + u 1)] : Fin 3 → ℝ) b = 0
  simp [Fin.sum_univ_three]

theorem nativeFrameEntries_surjective_of_zero_sum (v : Fin 3 → ℝ) (hv : ∑ b, v b = 0) :
    ∃ u, nativeFrameEntries u = v := by
  refine ⟨![v 0, v 1], ?_⟩
  have hh : -(v 0 + v 1) = v 2 := by
    rw [Fin.sum_univ_three] at hv
    linarith
  change ![v 0, v 1, -(v 0 + v 1)] = v
  funext b
  fin_cases b <;> simp [hh]

def nativeFrameChart (p : Fin 3 → Glennie.Albert) : (Fin 2 → ℝ) →ₗ[ℝ] NativeTraceless :=
  nativeCenter.comp ((nativeFrameSynthesis p).comp nativeFrameEntries)

theorem nativeFrameChart_coe {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (u : Fin 2 → ℝ) :
    (nativeFrameChart p u : Glennie.Albert) = nativeFrameSynthesis p (nativeFrameEntries u) := by
  change Glennie.traceless (nativeFrameSynthesis p (nativeFrameEntries u)) = _
  simp [Glennie.traceless, nativeFrameSynthesis_trace hp, nativeFrameEntries_sum]

theorem nativeFrameChart_injective {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    Function.Injective (nativeFrameChart p) := by
  intro u v huv
  have h := congrArg Subtype.val huv
  rw [nativeFrameChart_coe hp, nativeFrameChart_coe hp] at h
  have hentry (i : Fin 3) : nativeFrameEntries u i = nativeFrameEntries v i := by
    simpa only [nativeFrame_analysis_synthesis hp] using congrArg (Glennie.inner (p i)) h
  funext i
  fin_cases i
  · exact hentry 0
  · exact hentry 1

def nativeFramePlane (p : Fin 3 → Glennie.Albert) : Submodule ℝ NativeTraceless :=
  LinearMap.range (nativeFrameChart p)

theorem nativeFramePlane_dimension {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    Module.finrank ℝ (nativeFramePlane p) = 2 := by
  rw [nativeFramePlane, LinearMap.finrank_range_of_inj (nativeFrameChart_injective hp)]
  simp

theorem nativeFramePlane_closed {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    {x y : NativeTraceless} (hx : x ∈ nativeFramePlane p) (hy : y ∈ nativeFramePlane p) :
    nativeCenteredJordan x y ∈ nativeFramePlane p := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  let w := fun b => nativeFrameEntries u b * nativeFrameEntries v b
  have hsum : ∑ b : Fin 3, (w b - (∑ c, w c) / 3) = 0 := by
    simp only [Fin.sum_univ_three]
    ring
  obtain ⟨z, hz⟩ := nativeFrameEntries_surjective_of_zero_sum _ hsum
  refine ⟨z, Subtype.ext ?_⟩
  rw [nativeFrameChart_coe hp, nativeCenteredJordan_apply, nativeCenter_coe,
    nativeFrameChart_coe hp, nativeFrameChart_coe hp, nativeFrameSynthesis_jordan hp,
    nativeFrameSynthesis_centered hp, hz]

theorem TightNativeCode.planes_orthogonal (c : TightNativeCode) :
    Pairwise fun f g : Fin 13 => Submodule.IsOrtho (𝕜 := ℝ) (E := NativeTraceless)
      (nativeFramePlane (c.point f)) (nativeFramePlane (c.point g)) := by
  intro f g hfg
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
  change Glennie.inner (nativeFrameChart (c.point f) u) (nativeFrameChart (c.point g) v) = 0
  rw [nativeFrameChart_coe (c.frame f), nativeFrameChart_coe (c.frame g), nativeFrameSynthesis_inner]
  apply Finset.sum_eq_zero
  intro a _
  rw [nativeFrame_inner_synthesis]
  simp only [c.overlap hfg]
  rw [← Finset.sum_mul, nativeFrameEntries_sum, zero_mul, mul_zero]

end ThirteenPlanes
