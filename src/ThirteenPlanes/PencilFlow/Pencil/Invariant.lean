module

public import ThirteenPlanes.PencilFlow.Pencil.Tangency
public import ThirteenPlanes.CubicAnalysis
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

/-! The one-loop invariance of the pencil, invariance: a solution of the ambient tensor equation on
`[0, T]` that starts in the pencil stays in it.

Route (different from the printed one-line remark, which leaves uniqueness implicit): let `π` be
the orthogonal projection onto the pencil `W` in the coefficient metric, and `e = h - π h`. Since
the smooth field `F` maps `W` into `W`, `e' = (1 - π)(F h - F (π h))`, so `‖e'‖ ≤ 2K‖e‖` with `K` a
Lipschitz constant of `F` on a ball containing the compact trajectory; Grönwall gives `e = 0`. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace
open Set Metric

namespace ThirteenPlanes.PencilFlow.Pencil

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth autonomous field that maps a subspace into itself leaves it invariant along any
solution on a compact forward interval. -/
theorem subspace_invariant_of_tangent {F : E → E} (hF : ContDiff ℝ 1 F) (W : Submodule ℝ E)
    (htan : ∀ y ∈ W, F y ∈ W) {T : ℝ} {γ : ℝ → E}
    (hγ : IsIntegralCurveOn γ (fun _ => F) (Icc 0 T)) (h0 : γ 0 ∈ W) :
    ∀ s ∈ Icc 0 T, γ s ∈ W := by
  let π := W.starProjection
  have hcont : ContinuousOn γ (Icc 0 T) := hγ.continuousOn
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp
    (isCompact_Icc.image_of_continuousOn hcont).isBounded
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) R) (isCompact_closedBall _ _)
  have hball : ∀ t ∈ Icc 0 T, γ t ∈ closedBall (0 : E) R := fun t ht =>
    hR (mem_image_of_mem γ ht)
  have hballπ : ∀ t ∈ Icc 0 T, π (γ t) ∈ closedBall (0 : E) R := by
    intro t ht
    have h1 := hball t ht
    rw [mem_closedBall_zero_iff] at h1 ⊢
    exact (W.norm_starProjection_apply_le (γ t)).trans h1
  let e : ℝ → E := fun t => γ t - π (γ t)
  let e' : ℝ → E := fun t => F (γ t) - π (F (γ t))
  have he : ∀ t ∈ Icc 0 T, e t = 0 := by
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f' := e') (K := 2 * K)
      (hcont.sub (π.continuous.comp_continuousOn hcont)) ?_ ?_ ?_
    · intro t ht
      have hd : HasDerivWithinAt γ (F (γ t)) (Ici t) t :=
        (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      exact hd.sub (π.hasFDerivAt.comp_hasDerivWithinAt t hd)
    · have hπ0 : π (γ 0) = γ 0 := W.starProjection_eq_self_iff.mpr h0
      simp only [e, hπ0, sub_self]
    · intro t ht
      have ht' := Ico_subset_Icc_self ht
      have hW : F (π (γ t)) ∈ W := htan _ (W.starProjection_apply_mem _)
      have hfix : π (F (π (γ t))) = F (π (γ t)) := W.starProjection_eq_self_iff.mpr hW
      have hrw : e' t = (F (γ t) - F (π (γ t))) - π (F (γ t) - F (π (γ t))) := by
        simp only [e', map_sub, hfix]
        abel
      have hlip : ‖F (γ t) - F (π (γ t))‖ ≤ K * ‖e t‖ := by
        have := hK.norm_sub_le (hball t ht') (hballπ t ht')
        simpa only [e] using this
      rw [hrw]
      calc
        _ ≤ ‖F (γ t) - F (π (γ t))‖ + ‖π (F (γ t) - F (π (γ t)))‖ := norm_sub_le _ _
        _ ≤ ‖F (γ t) - F (π (γ t))‖ + ‖F (γ t) - F (π (γ t))‖ := by
          gcongr
          exact W.norm_starProjection_apply_le _
        _ ≤ 2 * K * ‖e t‖ := by linarith
  intro s hs
  have hs0 := he s hs
  have hmem : π (γ s) ∈ W := W.starProjection_apply_mem _
  have : γ s = π (γ s) := sub_eq_zero.mp hs0
  rw [this]
  exact hmem

end

end ThirteenPlanes.PencilFlow.Pencil

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements

/-- The one-loop invariance of the pencil: tangency and invariance of the pencil. -/
theorem pencilInvariant (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.PencilInvariant V := by
  intro m _ h c planes round closed ε
  have htan := Pencil.closedPencil_tangent h c planes round closed ε
  refine ⟨htan, fun T _ γ hγ h0 => ?_⟩
  refine Pencil.subspace_invariant_of_tangent (oneLoopBeta_contDiff 1 ε)
    (LinearMap.range (coupling (planePencil h planes))) ?_ hγ h0
  rintro y ⟨u, rfl⟩
  exact ⟨_, (htan u).symm⟩

end ThirteenPlanes.PencilFlow.Proofs
