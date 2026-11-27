module

public import ThirteenPlanes.Peirce.Clifford

@[expose] public section

/-! Axial coordinates for the two reducible Peirce cases of a normalized round cubic. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.Nonharmonic

open Module.End Peirce Submodule

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A unit idempotent with zero half space is an axis of the normalized reducible cubic. -/
theorem normalForm_of_half_bot (h : SymmetricCubic V) (round : IsRound h 1)
    {a : V} (ha : IsUnitIdempotent h a) (hH : halfSpace h a = ⊥) :
    ∀ x : V, let s := ⟪x, a⟫
      h.apply x x x = s ^ 3 - 3 * s * ‖x - s • a‖ ^ 2 := by
  intro x
  let s : ℝ := ⟪x, a⟫
  let y : V := x - s • a
  change h.apply x x x = s ^ 3 - 3 * s * ‖y‖ ^ 2
  have hya : ⟪y, a⟫ = 0 := by
    simp [y, s, inner_sub_left, real_inner_smul_left, ha.norm_eq_one]
  have hay : ⟪a, y⟫ = 0 := (real_inner_comm _ _).trans hya
  have hy : y ∈ minusSpace h a := by
    have hp := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hya
    rw [← (spectralSplit round ha).perp_split, hH, sup_bot_eq] at hp
    exact hp
  have hyL : h.L a y = -y := by simpa using mem_eigenspace_iff.mp hy
  have hyL' : h.L y a = -y := (h.L_comm y a).trans hyL
  have hyy : h.L y y = (-‖y‖ ^ 2) • a := by
    rw [minus_mul_minus round ha hy hy, real_inner_self_eq_norm_sq]
  have hxy : x = s • a + y := by
    dsimp [y]
    abel
  have hsquare : h.L (s • a + y) (s • a + y) =
      (s ^ 2 - ‖y‖ ^ 2) • a - (2 * s) • y := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      ha.square_eq_self, hyL, hyL', hyy]
    module
  calc
    h.apply x x x = h.apply (s • a + y) (s • a + y) (s • a + y) :=
      congrArg (fun v => h.apply v v v) hxy
    _ = s ^ 3 - 3 * s * ‖y‖ ^ 2 := by
      rw [SymmetricCubic.apply, hsquare]
      simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, ha.norm_eq_one, hay, hya, one_pow]
      ring

variable [FiniteDimensional ℝ V]

/-- Rotating the axis in the line and minus plane places the scalar half-action case
in the zero-half-space case. -/
theorem normalForm_of_minus_line (h : SymmetricCubic V) (round : IsRound h 1)
    {a : V} (ha : IsUnitIdempotent h a) (u : minusSpace h a) (hu : ‖u‖ = 1)
    (hM : Module.finrank ℝ (minusSpace h a) = 1) {r : ℝ} (hr : r ^ 2 = 3 / 4)
    (hscalar : ∀ y : halfSpace h a, halfAction round ha u y = r • y) :
    let e := (-1 / 2 : ℝ) • a - r • (u : V)
    ‖e‖ = 1 ∧ ∀ x : V, let s := ⟪x, e⟫
      h.apply x x x = s ^ 3 - 3 * s * ‖x - s • e‖ ^ 2 := by
  let e := (-1 / 2 : ℝ) • a - r • (u : V)
  change ‖e‖ = 1 ∧ _
  have split := spectralSplit round ha
  have hnu : ‖(u : V)‖ = 1 := hu
  have hau : ⟪a, (u : V)⟫ = 0 := split.minus_perp.inner_eq (mem_span_singleton_self a) u.property
  have hua : ⟪(u : V), a⟫ = 0 := (real_inner_comm _ _).trans hau
  have hea : ⟪e, a⟫ = -1 / 2 := by
    simp [e, inner_sub_left, real_inner_smul_left, hua, ha.norm_eq_one]
  have heu : ⟪e, (u : V)⟫ = -r := by
    simp [e, inner_sub_left, real_inner_smul_left, hau, hnu]
  have heinner : ⟪e, e⟫ = 1 := by
    change ⟪e, (-1 / 2 : ℝ) • a - r • (u : V)⟫ = 1
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, hea, heu]
    nlinarith only [hr]
  have hne : ‖e‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at heinner
    rw [← Real.sqrt_sq (norm_nonneg e), heinner, Real.sqrt_one]

  let P : V →ₗ[ℝ] V := (2 : ℝ) • (innerSL ℝ e).toLinearMap.smulRight e - LinearMap.id
  have hP (x : V) : P x = (2 * ⟪e, x⟫) • e - x := by
    change (2 : ℝ) • (⟪e, x⟫ • e) - x = _
    rw [smul_smul]
  have hauL : h.L a (u : V) = -(u : V) := by simpa using mem_eigenspace_iff.mp u.property
  have huaL : h.L (u : V) a = -(u : V) := (h.L_comm _ _).trans hauL
  have huu : h.L (u : V) (u : V) = -a := by
    rw [minus_mul_minus round ha u.property u.property, real_inner_self_eq_norm_sq, hnu]
    norm_num
  have haP : h.L e a = P a := by
    rw [hP, hea]
    simp only [e, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      ha.square_eq_self, huaL]
    module
  have huP : h.L e (u : V) = P (u : V) := by
    rw [hP, heu]
    simp only [e, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      hauL, huu, smul_sub, smul_smul]
    have hcoef : 2 * -r * r = -(3 / 2) := by nlinarith only [hr]
    rw [hcoef]
    module
  have hyP (y : V) (hy : y ∈ halfSpace h a) : h.L e y = P y := by
    have hay := split.half_perp.inner_eq (mem_span_singleton_self a) hy
    have huy := split.minus_half_perp.inner_eq u.property hy
    have hey : ⟪e, y⟫ = 0 := by simp [e, inner_sub_left, real_inner_smul_left, hay, huy]
    have hayL : h.L a y = (1 / 2 : ℝ) • y := mem_eigenspace_iff.mp hy
    have huyL : h.L (u : V) y = r • y := congrArg Subtype.val (hscalar ⟨y, hy⟩)
    rw [hP, hey, mul_zero, zero_smul, zero_sub]
    simp only [e, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      hayL, huyL, smul_smul]
    have hcoef : r * r = 3 / 4 := by nlinarith only [hr]
    rw [hcoef]
    module

  have hu_ne : (u : V) ≠ 0 := by
    intro hu0
    simp [hu0] at hnu
  have hspan : (ℝ ∙ (u : V)) = minusSpace h a := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr u.property)
    · rw [hM, finrank_span_singleton hu_ne]
  have hLe : h.L e = P := by
    ext x
    have hx : x ∈ (ℝ ∙ a) ⊔ ((ℝ ∙ (u : V)) ⊔ halfSpace h a) := by
      rw [hspan, split.full_split]
      trivial
    obtain ⟨a₁, ha₁, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ha₁
    obtain ⟨u₁, hu₁, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
    simp only [map_add, map_smul, haP, huP, hyP y hy]
  have he : IsUnitIdempotent h e := ⟨hne, by
    rw [hLe, hP, heinner]
    module⟩
  have hhalf : halfSpace h e = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    have hey := (spectralSplit round he).half_perp.inner_eq (mem_span_singleton_self e) hy
    have hyL : h.L e y = (1 / 2 : ℝ) • y := mem_eigenspace_iff.mp hy
    rw [hLe, hP, hey, mul_zero, zero_smul, zero_sub] at hyL
    have hy0 : (-3 / 2 : ℝ) • y = 0 := calc
      _ = -y - (1 / 2 : ℝ) • y := by module
      _ = 0 := sub_eq_zero.mpr hyL
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.mp hy0).resolve_left (by norm_num)
  exact ⟨hne, normalForm_of_half_bot h round he hhalf⟩

end

end ThirteenPlanes.Nonharmonic
