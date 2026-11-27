module

public import ThirteenPlanes.Peirce.Clifford

@[expose] public section

set_option backward.privateInPublic true

/-! Traces of multiplication on the Peirce summands of a normalized round cubic. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {a : V}

private def compression (U : Submodule ℝ V) (T : Module.End ℝ V) : Module.End ℝ U :=
  (U.orthogonalProjectionOnto.toLinearMap.comp T).comp U.subtype

private theorem compression_eq_zero_of_orthogonal (U : Submodule ℝ V) (T : Module.End ℝ V)
    (hU : ∀ x ∈ U, T x ∈ Uᗮ) : compression U T = 0 := by
  apply LinearMap.ext
  intro x
  change U.orthogonalProjectionOnto (T x) = 0
  exact Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (hU x x.property)

private theorem peirceProjections_sum (ss : SpectralSplit h a) :
    (ℝ ∙ a).starProjection.toLinearMap + (minusSpace h a).starProjection.toLinearMap +
      (halfSpace h a).starProjection.toLinearMap = LinearMap.id := by
  have vanish {U W : Submodule ℝ V} (orth : U.IsOrtho W) {x : V} (hx : x ∈ U) :
      W.starProjection x = 0 := by
    apply Submodule.eq_starProjection_of_mem_orthogonal (K := W) (Submodule.zero_mem W)
    simpa only [sub_zero] using orth.le hx
  apply LinearMap.ext
  intro x
  have hx : x ∈ (ℝ ∙ a) ⊔ (minusSpace h a ⊔ halfSpace h a) := by
    rw [ss.full_split]
    trivial
  obtain ⟨p, hp, rest, hrest, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp hrest
  simp only [LinearMap.add_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply, map_add]
  rw [Submodule.starProjection_eq_self_iff.mpr hp, Submodule.starProjection_eq_self_iff.mpr hu,
    Submodule.starProjection_eq_self_iff.mpr hy,
    vanish ss.minus_perp hp, vanish ss.half_perp hp,
    vanish ss.minus_perp.symm hu, vanish ss.half_perp.symm hy,
    vanish ss.minus_half_perp hu, vanish ss.minus_half_perp.symm hy]
  abel

private theorem trace_projection_comp (U : Submodule ℝ V) (T : Module.End ℝ V) :
    LinearMap.trace ℝ V (U.starProjection.toLinearMap.comp T) =
      LinearMap.trace ℝ U (compression U T) := by
  change LinearMap.trace ℝ V (U.subtype.comp (U.orthogonalProjectionOnto.toLinearMap.comp T)) = _
  exact LinearMap.trace_comp_comm' _ _

private theorem trace_eq_peirceCompressions (ss : SpectralSplit h a) (T : Module.End ℝ V) :
    LinearMap.trace ℝ V T =
      LinearMap.trace ℝ (ℝ ∙ a) (compression (ℝ ∙ a) T) +
        LinearMap.trace ℝ (minusSpace h a) (compression (minusSpace h a) T) +
        LinearMap.trace ℝ (halfSpace h a) (compression (halfSpace h a) T) := by
  calc
    LinearMap.trace ℝ V T =
        LinearMap.trace ℝ V (((ℝ ∙ a).starProjection.toLinearMap +
          (minusSpace h a).starProjection.toLinearMap +
          (halfSpace h a).starProjection.toLinearMap).comp T) := by
      rw [peirceProjections_sum ss, LinearMap.id_comp]
    _ = _ := by
      rw [LinearMap.add_comp, LinearMap.add_comp, map_add, map_add,
        trace_projection_comp, trace_projection_comp, trace_projection_comp]

private theorem compression_line_eq_zero {x : V} {r : ℝ} (hx : h.L a x = r • x)
    (horth : x ∈ (ℝ ∙ a)ᗮ) : compression (ℝ ∙ a) (h.L x) = 0 := by
  apply compression_eq_zero_of_orthogonal
  intro w hw
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, h.L_comm x a, hx]
  exact (ℝ ∙ a)ᗮ.smul_mem _ ((ℝ ∙ a)ᗮ.smul_mem _ horth)

/-- Multiplication by a vector in the half Peirce space has zero trace. -/
theorem trace_L_half_eq_zero (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    (y : halfSpace h a) : LinearMap.trace ℝ V (h.L (y : V)) = 0 := by
  have ss := spectralSplit round ha
  have hline : compression (ℝ ∙ a) (h.L (y : V)) = 0 :=
    compression_line_eq_zero (Module.End.mem_eigenspace_iff.mp y.property)
      (ss.half_perp.symm.le y.property)
  have hminus : compression (minusSpace h a) (h.L (y : V)) = 0 := by
    apply compression_eq_zero_of_orthogonal
    intro u hu
    rw [h.L_comm (y : V) u]
    exact ss.minus_half_perp.symm.le (minus_mul_half round ha hu y.property)
  have hhalf : compression (halfSpace h a) (h.L (y : V)) = 0 := by
    apply compression_eq_zero_of_orthogonal
    intro x hx
    rw [Submodule.mem_orthogonal']
    intro z hz
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) y.property hx hz
  rw [trace_eq_peirceCompressions ss, hline, hminus, hhalf]
  simp

/-- For multiplication by a minus Peirce vector, only the half-space action contributes
to the trace. -/
theorem trace_L_minus_eq_trace_halfAction (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    (u : minusSpace h a) :
    LinearMap.trace ℝ V (h.L (u : V)) = LinearMap.trace ℝ (halfSpace h a) (halfAction round ha u) := by
  have ss := spectralSplit round ha
  have hline : compression (ℝ ∙ a) (h.L (u : V)) = 0 :=
    compression_line_eq_zero (Module.End.mem_eigenspace_iff.mp u.property)
      (ss.minus_perp.symm.le u.property)
  have hminus : compression (minusSpace h a) (h.L (u : V)) = 0 := by
    apply compression_eq_zero_of_orthogonal
    intro v hv
    rw [minus_mul_minus round ha u.property hv]
    exact (minusSpace h a)ᗮ.smul_mem _
      (ss.minus_perp.le (Submodule.mem_span_singleton_self a))
  have hhalf : compression (halfSpace h a) (h.L (u : V)) = halfAction round ha u := by
    apply LinearMap.ext
    intro y
    change (halfSpace h a).orthogonalProjectionOnto (h.L (u : V) (y : V)) = halfAction round ha u y
    rw [← halfAction_apply_coe round ha u y, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [trace_eq_peirceCompressions ss, hline, hminus, hhalf]
  simp

/-- Vanishing trace on the idempotent and all half-space Clifford actions forces the
ambient cubic to be trace-free. -/
theorem traceFree_of_balanced (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    (hA : LinearMap.trace ℝ V (h.L a) = 0)
    (hM : ∀ u : minusSpace h a, LinearMap.trace ℝ (halfSpace h a) (halfAction round ha u) = 0) :
    h.TraceFree := by
  intro x
  have ss := spectralSplit round ha
  have hx : x ∈ (ℝ ∙ a) ⊔ (minusSpace h a ⊔ halfSpace h a) := by
    rw [ss.full_split]
    trivial
  obtain ⟨p, hp, rest, hrest, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp hrest
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hp
  have hu0 : LinearMap.trace ℝ V (h.L u) = 0 :=
    (trace_L_minus_eq_trace_halfAction round ha ⟨u, hu⟩).trans (hM ⟨u, hu⟩)
  have hy0 : LinearMap.trace ℝ V (h.L y) = 0 :=
    trace_L_half_eq_zero round ha ⟨y, hy⟩
  simp only [map_add, map_smul, hA, hu0, hy0, smul_zero, add_zero]

end
end ThirteenPlanes.Peirce
