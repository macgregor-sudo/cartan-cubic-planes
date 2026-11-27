module

public import ThirteenPlanes.PlanePencilSplit
public import ThirteenPlanes.MixedProducts
public import ThirteenPlanes.Energy

@[expose] public section

set_option backward.privateInPublic true

/-! The directional energy identity for the closed-plane pencil. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

open SymmetricCubic PlaneContractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {c : ℝ}
  {ι : Type*} [Fintype ι] {planes : PlaneDecomposition V ι}

/-- The energy of the intrinsic pencil in single-plane units. -/
noncomputable def normalizedPencilEnergy (h : SymmetricCubic V) (planes : PlaneDecomposition V ι)
    (c t : ℝ) (x : V) : ℝ :=
  ‖(interactionCubic (planePencil h planes) t).squareMap x‖ ^ 2 / c

private theorem diagonal_sq_norm (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (x : V) : ‖(planePencil h planes).diagonalCubic.squareMap x‖ ^ 2 =
      c * ∑ i, ‖planes.proj i x‖ ^ 4 := by
  let d (i : ι) : planes.plane i :=
    ⟨h.L (planes.proj i x) (planes.proj i x),
      closed i (piP planes i x).property (piP planes i x).property⟩
  have hfam : OrthogonalFamily ℝ (fun i => planes.plane i)
      (fun i => (planes.plane i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise planes.pairwise_orthogonal
  rw [planePencil_diagonal_sq closed]
  change ‖∑ i, (planes.plane i).subtypeₗᵢ (d i)‖ ^ 2 = _
  rw [hfam.norm_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => round.square_norm (planes.proj i x)

/-- The directional identity in plane-pencil energy formula, at arbitrary positive round strength. -/
theorem planePencil_directional_energy (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (t : ℝ) (x : V) (hx : ‖x‖ = 1) :
    normalizedPencilEnergy h planes c t x - 1 =
      (t - 1) * (1 - (∑ i, ‖planes.proj i x‖ ^ 4) +
        t / c * ‖(planePencil h planes).mixingCubic.squareMap x‖ ^ 2) := by
  let D := (planePencil h planes).diagonalCubic.squareMap x
  let M := (planePencil h planes).mixingCubic.squareMap x
  have hsq (s : ℝ) :
      (interactionCubic (planePencil h planes) s).squareMap x = D + s • M := by
    simp only [interactionCubic, coupling_apply, one_smul, squareMap_add, squareMap_smul, D, M]
  have hr : ‖D + M‖ ^ 2 = c := by
    have hr := round.square_norm x
    rw [← planePencil_at_one h planes, hsq, one_smul, hx, one_pow, mul_one] at hr
    exact hr
  rw [norm_add_sq_real] at hr
  have hd : ‖D‖ ^ 2 = c * ∑ i, ‖planes.proj i x‖ ^ 4 := diagonal_sq_norm round closed x
  unfold normalizedPencilEnergy
  rw [hsq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  change (‖D‖ ^ 2 + 2 * (t * ⟪D, M⟫) + t ^ 2 * ‖M‖ ^ 2) / c - 1 =
    (t - 1) * (1 - (∑ i, ‖planes.proj i x‖ ^ 4) + t / c * ‖M‖ ^ 2)
  field_simp [round.positive.ne']
  linear_combination t * hr + (1 - t) * hd

private theorem pencil_L (t : ℝ) (x y : V) :
    (interactionCubic (planePencil h planes) t).L x y =
      (planePencil h planes).diagonalCubic.L x y +
        t • (planePencil h planes).mixingCubic.L x y := by
  rw [interactionCubic, coupling_apply, one_smul, map_add, map_smul,
    LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]

private theorem mixing_L (x y : V) :
    (planePencil h planes).mixingCubic.L x y =
      h.L x y - (planePencil h planes).diagonalCubic.L x y := by
  change (h - (planePencil h planes).diagonalCubic).L x y = _
  rw [map_sub (SymmetricCubic.L (V := V)), LinearMap.sub_apply, LinearMap.sub_apply]

private theorem pencil_L_same (closed : IsClosedPlaneSystem h planes) (t : ℝ) (i : ι)
    (x y : planes.plane i) :
    (interactionCubic (planePencil h planes) t).L x y = h.L x y := by
  have hz : (planePencil h planes).mixingCubic.L x y = 0 := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_zero_left]
    exact planePencil_mixing_repeated closed i x y w
  have hd := sub_eq_zero.mp ((mixing_L (h := h) (planes := planes) x y).symm.trans hz)
  rw [pencil_L, hz, smul_zero, add_zero, ← hd]

private theorem pencil_L_distinct (t : ℝ) {i j : ι} (hij : i ≠ j) (x : planes.plane i)
    (y : planes.plane j) :
    (interactionCubic (planePencil h planes) t).L x y = t • h.L x y := by
  have hd : (planePencil h planes).diagonalCubic.L x y = 0 := by
    classical
    apply ext_inner_right ℝ
    intro w
    rw [inner_zero_left]
    change (planePencil h planes).diagonalCubic.apply x y w = 0
    have hD : (planePencil h planes).diagonalCubic = ∑ k, h.pullback (planes.proj k) := rfl
    rw [hD, apply_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pullback_apply]
    by_cases hki : k = i
    · subst k
      have hz : planes.proj i y = 0 :=
        congrArg Subtype.val (LinearMap.congr_fun (piP_subtype_ne planes hij) y)
      rw [hz]
      change ⟪h.L _ 0, _⟫ = 0
      rw [map_zero, inner_zero_left]
    · have hz : planes.proj k x = 0 :=
        congrArg Subtype.val (LinearMap.congr_fun (piP_subtype_ne planes hki) x)
      rw [hz]
      change ⟪h.L 0 _, _⟫ = 0
      rw [map_zero, LinearMap.zero_apply, inner_zero_left]
  rw [pencil_L, mixing_L, hd, sub_zero, zero_add]

omit [FiniteDimensional ℝ V] in
private theorem squareMap_smul_vector (g : SymmetricCubic V) (r : ℝ) (x : V) :
    g.squareMap (r • x) = r ^ 2 • g.squareMap x := by
  change g.L (r • x) (r • x) = r ^ 2 • g.L x x
  rw [map_smul g.L, LinearMap.smul_apply, map_smul, smul_smul, pow_two]

omit [FiniteDimensional ℝ V] in
private theorem isRound_of_unit_square (g : SymmetricCubic V) (hc : 0 < c)
    (hg : ∀ x : V, ‖x‖ = 1 → ‖g.squareMap x‖ ^ 2 = c) : IsRound g c := by
  refine ⟨hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, squareMap]
  let u := ‖x‖⁻¹ • x
  have hn : ‖x‖ ≠ 0 := (norm_pos_iff.2 hx).ne'
  have hu : ‖u‖ = 1 := by
    change ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]
  have hs : ‖x‖ • u = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  conv_lhs => rw [← hs, squareMap_smul_vector]
  rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _), mul_pow, hg u hu, ← pow_mul]
  ring

omit [Fintype ι] in
private theorem plane_has_unit (i : ι) : ∃ x : planes.plane i, ‖(x : V)‖ = 1 := by
  let e := (stdOrthonormalBasis ℝ (planes.plane i)).reindex (finCongr (planes.dimension i))
  exact ⟨e 0, e.orthonormal.1 0⟩

omit [Fintype ι] in
private theorem plane_projection_eq_zero (i : ι) {w : V} (hw : w ∈ (planes.plane i)ᗮ) :
    piP planes i w = 0 :=
  Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hw

set_option maxHeartbeats 500000 in
/-- The strict constancy conclusion in plane-pencil energy formula for a system of at least two planes. -/
theorem planePencil_energy_constant_iff (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (hm : 1 < Fintype.card ι) (t : ℝ) :
    (∃ value, ConstantOnSphere (normalizedPencilEnergy h planes c t) value) ↔ t = 1 := by
  constructor
  · rintro ⟨value, hconst⟩
    let : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hm
    obtain ⟨j, k, hjk⟩ := exists_pair_ne ι
    obtain ⟨y, hy⟩ := plane_has_unit (planes := planes) j
    obtain ⟨z, hz⟩ := plane_has_unit (planes := planes) k
    let g := interactionCubic (planePencil h planes) t
    have hv : value = 1 := by
      have he := hconst y hy
      change ‖g.L (y : V) y‖ ^ 2 / c = value at he
      have hs := round.square_norm (y : V)
      rw [hy, one_pow, mul_one] at hs
      rw [show g.L (y : V) y = h.L (y : V) y from pencil_L_same closed t j y y,
        ← squareMap, hs, div_self round.positive.ne'] at he
      exact he.symm
    have rg : IsRound g c := by
      apply isRound_of_unit_square g round.positive
      intro x hx
      have he := hconst x hx
      change ‖g.squareMap x‖ ^ 2 / c = value at he
      rw [hv, div_eq_iff round.positive.ne', one_mul] at he
      exact he
    have cg : IsClosedPlaneSystem g planes := by
      intro i u v hu hv'
      have he := pencil_L_same closed t i (⟨u, hu⟩ : planes.plane i) ⟨v, hv'⟩
      change g.L u v = h.L u v at he
      rw [he]
      exact closed i hu hv'
    have horth := planes.pairwise_orthogonal hjk
    have hmixed := (mixedProductLaw round horth (closed j) (closed k)).1 y.property z.property
    have hnonzero : h.L (y : V) z ≠ 0 := by
      intro hzero
      have hn := hmixed.2
      rw [hzero, norm_zero, hy, hz] at hn
      nlinarith [round.positive]
    have ht : t ≠ 0 := by
      intro ht0
      have hn := ((mixedProductLaw rg horth (cg j) (cg k)).1 y.property z.property).2
      change 2 * ‖(interactionCubic (planePencil h planes) t).L (y : V) z‖ ^ 2 =
        c * ‖(y : V)‖ ^ 2 * ‖(z : V)‖ ^ 2 at hn
      rw [pencil_L_distinct t hjk y z, ht0, zero_smul, norm_zero, hy, hz] at hn
      nlinarith [round.positive]
    obtain ⟨i, hi⟩ : ∃ i, piP planes i (h.L (y : V) z) ≠ 0 := by
      by_contra! hp
      have hs := sum_proj_apply planes (h.L (y : V) z)
      simp only [proj_eq, LinearMap.comp_apply, hp, map_zero, Finset.sum_const_zero] at hs
      exact hnonzero hs.symm
    have hij : i ≠ j := by
      intro he
      apply hi
      rw [he]
      exact plane_projection_eq_zero j ((Submodule.orthogonal_le le_sup_left) hmixed.1)
    have hik : i ≠ k := by
      intro he
      apply hi
      rw [he]
      exact plane_projection_eq_zero k ((Submodule.orthogonal_le le_sup_right) hmixed.1)
    let w := piP planes i (h.L (y : V) z)
    obtain ⟨x, hs⟩ := (planeSquareModel round closed i).2.1 w
    have hA : ⟪h.L (x : V) x, h.L (y : V) z⟫ ≠ 0 := by
      rw [hs, ← inner_piP_left planes i w]
      intro hzero
      exact hi ((inner_self_eq_zero (𝕜 := ℝ)).mp hzero)
    have hxy := (planes.pairwise_orthogonal hij).inner_eq x.property y.property
    have hxz := (planes.pairwise_orthogonal hik).inner_eq x.property z.property
    have hyz := horth.inner_eq y.property z.property
    have hp := polarized round (x : V) x y z
    have hpg := polarized rg (x : V) x y z
    simp only [hxy, hxz, hyz, mul_zero, add_zero] at hp hpg
    change
      ⟪(interactionCubic (planePencil h planes) t).L (x : V) x,
        (interactionCubic (planePencil h planes) t).L (y : V) z⟫ +
      ⟪(interactionCubic (planePencil h planes) t).L (x : V) y,
        (interactionCubic (planePencil h planes) t).L (x : V) z⟫ +
      ⟪(interactionCubic (planePencil h planes) t).L (x : V) z,
        (interactionCubic (planePencil h planes) t).L (x : V) y⟫ = 0 at hpg
    rw [pencil_L_same closed t i x x, pencil_L_distinct t hjk y z,
      pencil_L_distinct t hij x y, pencil_L_distinct t hik x z] at hpg
    simp only [real_inner_smul_left, real_inner_smul_right] at hpg
    have hprod : t * (1 - t) * ⟪h.L (x : V) x, h.L (y : V) z⟫ = 0 := by
      linear_combination hpg - t ^ 2 * hp
    have hstrength : t * (1 - t) = 0 := (mul_eq_zero.mp hprod).resolve_right hA
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hstrength).resolve_left ht)).symm
  · rintro rfl
    refine ⟨1, fun x hx => ?_⟩
    exact sub_eq_zero.mp (by simpa using planePencil_directional_energy round closed 1 x hx)

/-- Both assertions of the plane-pencil energy formula for a complete system with at least two planes. -/
theorem planePencilEnergy (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (hm : 1 < Fintype.card ι) :
    (∀ (t : ℝ) (x : V), ‖x‖ = 1 →
      normalizedPencilEnergy h planes c t x - 1 =
        (t - 1) * (1 - (∑ i, ‖planes.proj i x‖ ^ 4) +
          t / c * ‖(planePencil h planes).mixingCubic.squareMap x‖ ^ 2)) ∧
    (∀ t : ℝ, (∃ value, ConstantOnSphere (normalizedPencilEnergy h planes c t) value) ↔ t = 1) :=
  ⟨planePencil_directional_energy round closed, planePencil_energy_constant_iff round closed hm⟩

end ThirteenPlanes.RoundCubics
