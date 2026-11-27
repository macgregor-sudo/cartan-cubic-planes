module

public import ThirteenPlanes.Recovery.Symmetry

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

/-- The kernel of the trace represented by the unit in the trace metric. -/
def traceZero (e : J) : Submodule ℝ J := (innerSL ℝ e).toLinearMap.ker

omit [FiniteDimensional ℝ J] in
theorem traceZero_inner {e : J} (x : traceZero e) : ⟪e, (x : J)⟫ = 0 :=
  x.property

/-- The unscaled trace cubic on the actual trace kernel. -/
def traceCubic (p : SymmetricCubic J) (e : J) : SymmetricCubic (traceZero e) :=
  p.pullback (traceZero e).subtype

private def traceJoin (e : J) : (traceZero e × ℝ) →ₗ[ℝ] J :=
  (traceZero e).subtype.coprod (LinearMap.toSpanSingleton ℝ J e)

omit [FiniteDimensional ℝ J] in
private theorem traceJoin_apply (e : J) (x : traceZero e) (r : ℝ) :
    traceJoin e (x, r) = x.val + r • e := rfl

private def traceJoinEquiv (e : J) (he : ⟪e, e⟫ = 3) : (traceZero e × ℝ) ≃ₗ[ℝ] J :=
  LinearEquiv.ofBijective (traceJoin e) ⟨by
    rintro ⟨x, r⟩ ⟨y, s⟩ h
    rw [traceJoin_apply, traceJoin_apply] at h
    have ht := congrArg (inner ℝ e) h
    rw [inner_add_right, inner_add_right, traceZero_inner x, traceZero_inner y,
      real_inner_smul_right, real_inner_smul_right, he] at ht
    have hrs : r = s := by linarith
    subst s
    exact Prod.ext (Subtype.ext (add_right_cancel h)) rfl, by
    intro z
    let r := ⟪e, z⟫ / 3
    have hc : z - r • e ∈ traceZero e := by
      change ⟪e, z - r • e⟫ = 0
      rw [inner_sub_right, real_inner_smul_right, he]
      dsimp [r]
      ring
    refine ⟨(⟨z - r • e, hc⟩, r), ?_⟩
    rw [traceJoin_apply, sub_add_cancel]⟩

private def extendTraceIsometry (e : J) (he : ⟪e, e⟫ = 3) (g : OrthogonalMap (traceZero e)) :
    J ≃ₗ[ℝ] J :=
  (traceJoinEquiv e he).symm.trans
    ((g.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)).trans (traceJoinEquiv e he))

private theorem extendTraceIsometry_join (e : J) (he : ⟪e, e⟫ = 3)
    (g : OrthogonalMap (traceZero e)) (x : traceZero e) (r : ℝ) :
    extendTraceIsometry e he g ((x : J) + r • e) = (g x : J) + r • e := by
  have hj := (traceJoinEquiv e he).symm_apply_apply (x, r)
  change (traceJoinEquiv e he).symm (traceJoin e (x, r)) = _ at hj
  rw [traceJoin_apply] at hj
  simp only [extendTraceIsometry, LinearEquiv.trans_apply, hj, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]
  rfl

private theorem exists_traceJoin (e : J) (he : ⟪e, e⟫ = 3) (x : J) :
    ∃ (u : traceZero e) (r : ℝ), (u : J) + r • e = x := by
  obtain ⟨⟨u, r⟩, hx⟩ := (traceJoinEquiv e he).surjective x
  exact ⟨u, r, hx⟩

private theorem extendTraceIsometry_inner {e : J} (he : ⟪e, e⟫ = 3)
    (g : OrthogonalMap (traceZero e)) (x y : J) :
    ⟪extendTraceIsometry e he g x, extendTraceIsometry e he g y⟫ = ⟪x, y⟫ := by
  obtain ⟨u, r, rfl⟩ := exists_traceJoin e he x
  obtain ⟨v, s, rfl⟩ := exists_traceJoin e he y
  have hs (a b : traceZero e) :
      ⟪(a : J) + r • e, (b : J) + s • e⟫ = ⟪(a : J), (b : J)⟫ + r * s * 3 := by
    have h0 : ⟪(a : J), e⟫ = 0 := (real_inner_comm _ _).trans (traceZero_inner a)
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      h0, traceZero_inner, he, mul_zero, zero_add, add_zero]
    ring
  rw [extendTraceIsometry_join, extendTraceIsometry_join, hs, hs]
  exact congrArg (fun b => b + r * s * 3) (g.inner_map_map u v)

private theorem extendTraceIsometry_unit {e : J} (he : ⟪e, e⟫ = 3)
    (g : OrthogonalMap (traceZero e)) : extendTraceIsometry e he g e = e := by
  simpa using extendTraceIsometry_join e he g 0 1

private theorem extendTraceIsometry_trace {e : J} (he : ⟪e, e⟫ = 3)
    (g : OrthogonalMap (traceZero e)) (x : J) :
    ⟪e, extendTraceIsometry e he g x⟫ = ⟪e, x⟫ := by
  calc
    _ = ⟪extendTraceIsometry e he g e, extendTraceIsometry e he g x⟫ := by
      rw [extendTraceIsometry_unit he g]
    _ = _ := extendTraceIsometry_inner he g e x

private theorem extendTraceIsometry_product {p : SymmetricCubic J} {e : J}
    (he : ⟪e, e⟫ = 3) (unit : ∀ x : J, p.L e x = x)
    (g : OrthogonalMap (traceZero e)) (hg : cubicPreserved (traceCubic p e) g) (x y : J) :
    extendTraceIsometry e he g (p.L x y) =
      p.L (extendTraceIsometry e he g x) (extendTraceIsometry e he g y) := by
  let F := extendTraceIsometry e he g
  apply ext_inner_right ℝ
  intro z
  obtain ⟨z, rfl⟩ := F.surjective z
  rw [show ⟪F (p.L x y), F z⟫ = ⟪p.L x y, z⟫ from extendTraceIsometry_inner he g _ _]
  change p.apply x y z = p.apply (F x) (F y) (F z)
  obtain ⟨u, r, rfl⟩ := exists_traceJoin e he x
  obtain ⟨v, s, rfl⟩ := exists_traceJoin e he y
  obtain ⟨w, t, rfl⟩ := exists_traceJoin e he z
  simp only [F, extendTraceIsometry_join, SymmetricCubic.apply_add₁,
    SymmetricCubic.apply_add₂, SymmetricCubic.apply_add₃, SymmetricCubic.apply_smul₁,
    SymmetricCubic.apply_smul₂, SymmetricCubic.apply_smul₃]
  have hp (a b : J) : p.apply e a b = ⟪a, b⟫ := by
    rw [SymmetricCubic.apply, unit]
  have hp₂ (a b : J) : p.apply a e b = ⟪a, b⟫ :=
    (p.apply_swap₁₂ _ _ _).trans (hp _ _)
  have hp₃ (a b : J) : p.apply a b e = ⟪a, b⟫ :=
    (p.apply_swap₂₃ _ _ _).trans (hp₂ _ _)
  have hh := (cubicPreserved_iff g).mp hg u v w
  simp only [traceCubic, SymmetricCubic.pullback_apply, Submodule.subtype_apply] at hh
  have hinner (a b : traceZero e) : ⟪(g a : J), (g b : J)⟫ = ⟪(a : J), (b : J)⟫ :=
    g.inner_map_map a b
  have hzero (a : traceZero e) : ⟪(a : J), e⟫ = 0 :=
    (real_inner_comm _ _).trans (traceZero_inner a)
  simp only [hp, hp₂, hp₃, hh, hinner, hzero, traceZero_inner, he, mul_zero, add_zero]

/-- Fixing the unit extends a trace-cubic isometry to a product and trace preserving automorphism.
Conversely such an automorphism restricts to the trace-cubic stabilizer. -/
theorem traceCubic_stabilizer_iff {p : SymmetricCubic J} {e : J}
    (he : ⟪e, e⟫ = 3) (unit : ∀ x : J, p.L e x = x)
    (g : OrthogonalMap (traceZero e)) :
    cubicPreserved (traceCubic p e) g ↔
    ∃ F : J ≃ₗ[ℝ] J, F e = e ∧ (∀ x y, F (p.L x y) = p.L (F x) (F y)) ∧
      (∀ x, ⟪e, F x⟫ = ⟪e, x⟫) ∧ ∀ x : traceZero e, F x = (g x : J) := by
  refine ⟨fun hg => ?_, ?_⟩
  · exact ⟨extendTraceIsometry e he g, extendTraceIsometry_unit he g,
      extendTraceIsometry_product he unit g hg, extendTraceIsometry_trace he g, fun x => by
        simpa using extendTraceIsometry_join e he g x 0⟩
  · rintro ⟨F, _, hmul, htrace, hrestrict⟩
    have hpair (x y : J) : ⟪F x, F y⟫ = ⟪x, y⟫ := by
      have hinner (a b : J) : ⟪e, p.L a b⟫ = ⟪a, b⟫ := by
        rw [real_inner_comm]
        change p.apply a b e = _
        rw [p.apply_swap₂₃, p.apply_swap₁₂, SymmetricCubic.apply, unit]
      rw [← hinner, ← hmul, htrace, hinner]
    apply (cubicPreserved_iff g).mpr
    intro x y z
    simp only [traceCubic, SymmetricCubic.pullback_apply, Submodule.subtype_apply, ← hrestrict]
    change ⟪p.L (F x) (F y), F z⟫ = ⟪p.L x y, (z : J)⟫
    rw [← hmul, hpair]

end
end ThirteenPlanes.RoundCubics
