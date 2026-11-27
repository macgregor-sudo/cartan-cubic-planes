module

public import ThirteenPlanes.BinaryPlane

@[expose] public section

set_option backward.privateInPublic true

/-! The diagonal and mixed products of a round cubic with closed orthogonal planes. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

open SymmetricCubic PlaneContractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {c : ℝ}
  {ι : Type*} {planes : PlaneDecomposition V ι}

omit [FiniteDimensional ℝ V] in
private theorem apply_square_model {g : SymmetricCubic V} (z : V ≃ₗᵢ[ℝ] ℂ)
    (hz : ∀ x, g.apply x x x = Real.sqrt c * ((z x) ^ 3).re) (x : V) :
    z (g.squareMap x) = Real.sqrt c • (star (z x)) ^ 2 := by
  apply ext_inner_right ℝ
  intro w
  obtain ⟨y, rfl⟩ := z.surjective w
  rw [z.inner_map_map, real_inner_smul_left, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  change g.apply x x y = Real.sqrt c * ((z y) * star ((star (z x)) ^ 2)).re
  rw [star_pow, star_star]
  have hcubic :
      g.apply (x + y) (x + y) (x + y) - g.apply (x - y) (x - y) (x - y) -
        2 * g.apply y y y = 6 * g.apply x x y := by
    have hxy : x - y = x + (-1 : ℝ) • y := by rw [neg_one_smul, sub_eq_add_neg]
    rw [hxy]
    have h₁ : g.apply x y x = g.apply x x y := g.apply_swap₂₃ _ _ _
    have h₂ : g.apply y x x = g.apply x x y := (g.apply_swap₁₂ _ _ _).trans h₁
    simp only [apply_add₁, apply_add₂, apply_add₃, apply_smul₁, apply_smul₂, apply_smul₃, h₁, h₂]
    ring
  rw [hz (x + y), hz (x - y), hz y, map_add, map_sub] at hcubic
  have hpoly := congrArg Complex.re (show
    (z x + z y) ^ 3 - (z x - z y) ^ 3 - 2 * (z y) ^ 3 =
      6 * (z y * (z x) ^ 2) from by ring)
  simp only [Complex.sub_re] at hpoly
  norm_num [Complex.mul_re] at hpoly ⊢
  norm_num [Complex.mul_re] at hcubic
  linear_combination -hcubic / 6 + Real.sqrt c * hpoly / 6

private theorem restriction_mul_coe (closed : IsClosedPlaneSystem h planes) (i : ι)
    (x y : planes.plane i) : ((planes.restriction i h).L x y : V) = h.L x y := by
  let w : planes.plane i := ⟨h.L x y, closed i x.property y.property⟩
  have hw : (planes.restriction i h).L x y = w := by
    apply ext_inner_right ℝ
    intro z
    change (planes.restriction i h).apply x y z = h.apply x y z
    exact planes.restriction_apply i h x y z
  exact congrArg Subtype.val hw

omit [FiniteDimensional ℝ V] in
private theorem traceFree_basis_sum {g : SymmetricCubic V} (tf : g.TraceFree)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) (y : V) :
    ∑ a, g.apply (e a) (e a) y = 0 := by
  rw [← tf y, ← sum_apply_diag e]
  exact Finset.sum_congr rfl fun a _ =>
    (g.apply_swap₂₃ _ _ _).trans (g.apply_swap₁₂ _ _ _)

/-- The square in a closed plane is conjugate squaring in orthonormal coordinates. -/
theorem planeSquareModel (round : IsRound h c) (closed : IsClosedPlaneSystem h planes) (i : ι) :
    (∃ z : planes.plane i ≃ₗᵢ[ℝ] ℂ, ∀ x : planes.plane i,
      z ⟨h.L x x, closed i x.property x.property⟩ = Real.sqrt c • (star (z x)) ^ 2) ∧
    (∀ y : planes.plane i, ∃ x : planes.plane i, h.L x x = (y : V)) ∧
    (∀ e : OrthonormalBasis (Fin 2) ℝ (planes.plane i),
      h.L (e 0) (e 0) + h.L (e 1) (e 1) = 0) := by
  let g := planes.restriction i h
  obtain ⟨tf, z, hz⟩ := binaryPlaneNormalForm (restriction_isRound round closed i)
    (planes.dimension i)
  have hs (x : planes.plane i) :
      z ⟨h.L x x, closed i x.property x.property⟩ = Real.sqrt c • (star (z x)) ^ 2 := by
    have hx : (⟨h.L x x, closed i x.property x.property⟩ : planes.plane i) = g.squareMap x :=
      Subtype.ext (restriction_mul_coe closed i x x).symm
    rw [hx, apply_square_model z hz]
  refine ⟨⟨z, hs⟩, ?_, ?_⟩
  · intro y
    have hc : (Real.sqrt c : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 round.positive).ne'
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (z y / (Real.sqrt c : ℂ)) (n := 2) (by decide)
    let x := z.symm (star u)
    have hx : (⟨h.L x x, closed i x.property x.property⟩ : planes.plane i) = y := by
      apply z.injective
      rw [hs x]
      change Real.sqrt c • (star (z (z.symm (star u)))) ^ 2 = z y
      rw [z.apply_symm_apply, star_star, hu, Complex.real_smul, mul_div_cancel₀ _ hc]
    exact ⟨x, congrArg Subtype.val hx⟩
  · intro e
    have hv : g.L (e 0) (e 0) + g.L (e 1) (e 1) = 0 := by
      apply ext_inner_right ℝ
      intro y
      have ht := traceFree_basis_sum tf e y
      rw [Fin.sum_univ_two] at ht
      rw [inner_add_left, inner_zero_left]
      change g.apply (e 0) (e 0) y + g.apply (e 1) (e 1) y = 0
      exact ht
    have hv' := congrArg Subtype.val hv
    simpa only [Submodule.coe_add, ZeroMemClass.coe_zero, g, restriction_mul_coe closed]
      using hv'

variable [Fintype ι]

omit [Fintype ι] in
private theorem proj_mem (i : ι) (x : V) : planes.proj i x ∈ planes.plane i :=
  (piP planes i x).property

/-- The diagonal square is the sum of the squares of the orthogonal components. -/
theorem planePencil_diagonal_sq (closed : IsClosedPlaneSystem h planes) (x : V) :
    (planePencil h planes).diagonalCubic.squareMap x =
      ∑ i, h.L (planes.proj i x) (planes.proj i x) := by
  have hd : (planePencil h planes).diagonalCubic = ∑ i, h.pullback (planes.proj i) := rfl
  rw [squareMap, L_diagonal hd, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ =>
    restriction_mul_coe closed i (piP planes i x) (piP planes i x)

omit [Fintype ι] in
private theorem proj_of_plane (i : ι) (x : planes.plane i) : planes.proj i x = (x : V) := by
  have he := LinearMap.congr_fun (piP_subtype planes i) x
  exact congrArg Subtype.val he

omit [Fintype ι] in
private theorem proj_of_other_plane {i j : ι} (hij : i ≠ j) (x : planes.plane j) :
    planes.proj i x = 0 := by
  have he := LinearMap.congr_fun (piP_subtype_ne planes hij) x
  exact congrArg Subtype.val he

/-- The mixed form vanishes when two arguments are in the same plane. -/
theorem planePencil_mixing_repeated (closed : IsClosedPlaneSystem h planes) (i : ι)
    (u v : planes.plane i) (w : V) : (planePencil h planes).mixingCubic.apply u v w = 0 := by
  classical
  let D := (planePencil h planes).diagonalCubic
  have hD : D = ∑ j, h.pullback (planes.proj j) := rfl
  have hproj : D.apply u v w = h.apply u v (planes.proj i w) := by
    rw [hD, apply_sum, Finset.sum_eq_single i]
    · rw [pullback_apply, proj_of_plane, proj_of_plane]
    · intro j _ hji
      rw [pullback_apply, proj_of_other_plane hji]
      change ⟪h.L 0 _ , _⟫ = 0
      rw [map_zero, LinearMap.zero_apply, inner_zero_left]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hclose : h.apply u v (planes.proj i w) = h.apply u v w := by
    let p : planes.plane i := ⟨h.L u v, closed i u.property v.property⟩
    exact inner_piP_left planes i p w
  change (h - D).apply u v w = 0
  have hm : (h - D).apply u v w = h.apply u v w - D.apply u v w := by
    rw [apply, apply, apply, map_sub (SymmetricCubic.L (V := V)), LinearMap.sub_apply,
      LinearMap.sub_apply, inner_sub_left]
  rw [hm, hproj, hclose, sub_self]

/-- The off-diagonal square, using ordered pairs of distinct planes. -/
theorem planePencil_mixing_sq (closed : IsClosedPlaneSystem h planes) (x : V) :
    (planePencil h planes).mixingCubic.squareMap x =
      (by
        classical
        exact ∑ i, ∑ j ∈ Finset.univ.erase i, h.L (planes.proj i x) (planes.proj j x)) := by
  classical
  have hsum : h.squareMap x = ∑ i, ∑ j, h.L (planes.proj i x) (planes.proj j x) := by
    conv_lhs => rw [squareMap, ← sum_proj_apply planes x]
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_comm
  have hpart (i : ι) :
      (∑ j, h.L (planes.proj i x) (planes.proj j x)) =
        h.L (planes.proj i x) (planes.proj i x) +
          ∑ j ∈ Finset.univ.erase i, h.L (planes.proj i x) (planes.proj j x) := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hm : (planePencil h planes).mixingCubic.squareMap x =
      h.squareMap x - (planePencil h planes).diagonalCubic.squareMap x := by
    change (h - (planePencil h planes).diagonalCubic).L x x = _
    rw [squareMap, squareMap, map_sub (SymmetricCubic.L (V := V)), LinearMap.sub_apply,
      LinearMap.sub_apply]
  rw [hm, hsum, planePencil_diagonal_sq closed]
  simp only [hpart, Finset.sum_add_distrib]
  abel

private theorem pencil_traceFree (round : IsRound h c) (closed : IsClosedPlaneSystem h planes) :
    h.TraceFree ∧ (planePencil h planes).diagonalCubic.TraceFree ∧
      (planePencil h planes).mixingCubic.TraceFree := by
  have htf := traceFree_of_isClosedPlaneSystem round closed
  have hd : (planePencil h planes).diagonalCubic.TraceFree :=
    trace_L_diag (planePencil_hasPlaneData round closed)
  refine ⟨htf, hd, fun x => ?_⟩
  change LinearMap.trace ℝ V ((h - (planePencil h planes).diagonalCubic).L x) = 0
  rw [map_sub (SymmetricCubic.L (V := V)), LinearMap.sub_apply, map_sub, htf x, hd x, sub_zero]

/-- The cubic tensor splitting for arbitrary positive strength. -/
theorem planePencilSplit (round : IsRound h c) (closed : IsClosedPlaneSystem h planes) :
    (∀ i, (∃ z : planes.plane i ≃ₗᵢ[ℝ] ℂ, ∀ x : planes.plane i,
      z ⟨h.L x x, closed i x.property x.property⟩ = Real.sqrt c • (star (z x)) ^ 2) ∧
      (∀ y : planes.plane i, ∃ x : planes.plane i, h.L x x = (y : V)) ∧
      (∀ e : OrthonormalBasis (Fin 2) ℝ (planes.plane i),
        h.L (e 0) (e 0) + h.L (e 1) (e 1) = 0)) ∧
    ((∀ x : V, (planePencil h planes).diagonalCubic.squareMap x =
      ∑ i, h.L (planes.proj i x) (planes.proj i x)) ∧
     (∀ i (x : V), h.L (planes.proj i x) (planes.proj i x) ∈ planes.plane i ∧
       ‖h.L (planes.proj i x) (planes.proj i x)‖ ^ 2 = c * ‖planes.proj i x‖ ^ 4) ∧
     (∀ i j (u v : planes.plane i) (w : planes.plane j),
       (planePencil h planes).mixingCubic.apply u v w = 0) ∧
     (∀ x : V, (planePencil h planes).mixingCubic.squareMap x =
       (by
         classical
         exact ∑ i, ∑ j ∈ Finset.univ.erase i, h.L (planes.proj i x) (planes.proj j x)))) ∧
    (∀ {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) (y : V),
      (∑ a, h.apply (e a) (e a) y) = 0 ∧
      (∑ a, (planePencil h planes).diagonalCubic.apply (e a) (e a) y) = 0 ∧
      (∑ a, (planePencil h planes).mixingCubic.apply (e a) (e a) y) = 0) := by
  refine ⟨planeSquareModel round closed, ⟨planePencil_diagonal_sq closed, ?_, ?_,
    planePencil_mixing_sq closed⟩, ?_⟩
  · intro i x
    exact ⟨closed i (proj_mem i x) (proj_mem i x), round.square_norm (planes.proj i x)⟩
  · intro i j u v w
    exact planePencil_mixing_repeated closed i u v w
  · intro κ _ e y
    obtain ⟨htf, hd, hm⟩ := pencil_traceFree round closed
    exact ⟨traceFree_basis_sum htf e y, traceFree_basis_sum hd e y, traceFree_basis_sum hm e y⟩

end ThirteenPlanes.RoundCubics
