module

public import ThirteenPlanes.Shares.RecoveryParameters
public import ThirteenPlanes.Shares.PlaneTransport
public import ThirteenPlanes.Shares.RecoverySign
public import ThirteenPlanes.PeirceDimensions

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace Classical
open PlaneContractions

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h g : SymmetricCubic V} {c : ℝ}

private theorem twoPlane_diagonal_sum (round : IsRound h c) (dim : Module.finrank ℝ V = 2)
    (e : OrthonormalBasis (Fin 2) ℝ V) :
    h.L (e 0) (e 0) + h.L (e 1) (e 1) = 0 := by
  have tf := traceFree_of_round_finrank_two round dim
  apply ext_inner_right ℝ
  intro z
  have he (x : V) : ⟪x, h.L z x⟫ = ⟪h.L x x, z⟫ :=
    (real_inner_comm _ _).trans ((h.apply_swap₁₂ z x x).trans (h.apply_swap₂₃ x z x))
  have ht := tf z
  rw [SymmetricCubic.trace_eq_sum_inner e, Fin.sum_univ_two, he, he] at ht
  simpa only [inner_add_left, inner_zero_left] using ht

private theorem twoPlane_product_basis (round : IsRound h c) (dim : Module.finrank ℝ V = 2)
    (e : OrthonormalBasis (Fin 2) ℝ V) :
    ∃ f : OrthonormalBasis (Fin 2) ℝ V, ∀ i, h.L (e 0) (e i) = Real.sqrt c • f i := by
  let a := h.L (e 0) (e 0)
  let b := h.L (e 0) (e 1)
  let d := Real.sqrt c
  have hd : 0 < d := Real.sqrt_pos.2 round.positive
  have hd2 : d ^ 2 = c := Real.sq_sqrt round.positive.le
  have hn0 : ‖e 0‖ = 1 := e.orthonormal.norm_eq_one 0
  have hn1 : ‖e 1‖ = 1 := e.orthonormal.norm_eq_one 1
  have he : ⟪e 0, e 1⟫ = 0 := by
    rw [orthonormal_iff_ite.mp e.orthonormal, ite_eq_right (by decide)]
  have ha : ‖a‖ ^ 2 = c := by simpa [a, SymmetricCubic.squareMap, hn0] using round.square_norm (e 0)
  have ha₁ : h.L (e 1) (e 1) = -a := by
    exact eq_neg_iff_add_eq_zero.mpr (by
      simpa only [add_comm] using twoPlane_diagonal_sum round dim e)
  have hb : ‖b‖ ^ 2 = c := by
    have hp := pair round (e 0) (e 1)
    rw [ha₁, inner_neg_right, real_inner_self_eq_norm_sq, ha, hn0, hn1, he] at hp
    change -c + 2 * ‖b‖ ^ 2 = c * (1 ^ 2 * 1 ^ 2 + 2 * 0 ^ 2) at hp
    linarith
  have hab : ⟪a, b⟫ = 0 := by
    have hp := polarized round (e 0) (e 0) (e 0) (e 1)
    have hcomm : ⟪b, a⟫ = ⟪a, b⟫ := by rw [real_inner_comm]
    change ⟪a, b⟫ + ⟪a, b⟫ + ⟪b, a⟫ = _ at hp
    simp only [he, mul_zero, zero_mul, add_zero, hcomm] at hp
    linarith
  let f (i : Fin 2) : V := d⁻¹ • h.L (e 0) (e i)
  have hf : Orthonormal ℝ f := by
    refine orthonormal_iff_ite.mpr fun i j => ?_
    have hscale : d⁻¹ * (d⁻¹ * c) = 1 := by
      rw [← hd2]
      field_simp [hd.ne']
    fin_cases i <;> fin_cases j
    · change ⟪d⁻¹ • a, d⁻¹ • a⟫ = 1
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, ha, hscale]
    · change ⟪d⁻¹ • a, d⁻¹ • b⟫ = 0
      rw [real_inner_smul_left, real_inner_smul_right, hab, mul_zero, mul_zero]
    · change ⟪d⁻¹ • b, d⁻¹ • a⟫ = 0
      have hba : ⟪b, a⟫ = 0 := (real_inner_comm _ _).trans hab
      rw [real_inner_smul_left, real_inner_smul_right, hba, mul_zero, mul_zero]
    · change ⟪d⁻¹ • b, d⁻¹ • b⟫ = 1
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hb, hscale]
  have htop : Submodule.span ℝ (Set.range f) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hf.linearIndependent, Fintype.card_fin, dim]
  refine ⟨OrthonormalBasis.mk hf htop.ge, fun i => ?_⟩
  rw [OrthonormalBasis.coe_mk]
  change h.L (e 0) (e i) = d • (d⁻¹ • h.L (e 0) (e i))
  rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]

private theorem twoPlane_product_output_isometry (rh : IsRound h c) (rg : IsRound g c)
    (dim : Module.finrank ℝ V = 2) :
    ∃ R : V ≃ₗᵢ[ℝ] V, ∀ x y : V, g.L x y = R (h.L x y) := by
  let e := (stdOrthonormalBasis ℝ V).reindex (finCongr dim)
  obtain ⟨f, hf⟩ := twoPlane_product_basis rh dim e
  obtain ⟨f', hf'⟩ := twoPlane_product_basis rg dim e
  let R := f.repr.trans f'.repr.symm
  have hr (i : Fin 2) : R (f i) = f' i := by
    apply f'.repr.injective
    simp [R]
  have first (i : Fin 2) : R (h.L (e 0) (e i)) = g.L (e 0) (e i) := by
    rw [hf, hf', map_smul, hr]
  have diag_h : h.L (e 1) (e 1) = -(h.L (e 0) (e 0)) :=
    eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using twoPlane_diagonal_sum rh dim e)
  have diag_g : g.L (e 1) (e 1) = -(g.L (e 0) (e 0)) :=
    eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using twoPlane_diagonal_sum rg dim e)
  have basis_apply (i j : Fin 2) : R (h.L (e i) (e j)) = g.L (e i) (e j) := by
    fin_cases i <;> fin_cases j
    · exact first 0
    · exact first 1
    · rw [h.L_comm, g.L_comm]
      exact first 1
    · change R (h.L (e 1) (e 1)) = g.L (e 1) (e 1)
      rw [diag_h, diag_g, map_neg, first]
  have row (i : Fin 2) : R.toLinearEquiv.toLinearMap.comp (h.L (e i)) = g.L (e i) :=
    e.toBasis.ext fun j => basis_apply i j
  refine ⟨R, fun x y => ?_⟩
  have hrow : g.L y = R.toLinearEquiv.toLinearMap.comp (h.L y) := by
    apply e.toBasis.ext
    intro i
    change g.L y (e i) = R (h.L y (e i))
    rw [g.L_comm, h.L_comm]
    exact (LinearMap.congr_fun (row i) y).symm
  rw [g.L_comm, hrow, LinearMap.comp_apply, h.L_comm]
  rfl

variable {ι : Type*} [Fintype ι] {planes : PlaneDecomposition V ι} {t : ℝ}

omit [Fintype ι] in
private theorem projection_mixed_eq_zero (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {j k : ι} (hjk : j ≠ k) (x : planes.plane j) (y : planes.plane k) :
    piP planes j (h.L (x : V) y) = 0 ∧ piP planes k (h.L (x : V) y) = 0 := by
  have hp := ((mixedProductLaw round (planes.pairwise_orthogonal hjk) (closed j) (closed k)).1
    x.property y.property).1
  exact ⟨Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (Submodule.orthogonal_le le_sup_left hp),
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (Submodule.orthogonal_le le_sup_right hp)⟩

/-- Equality of the actual triple energies at a nondegenerate parameter produces one
orthogonal output isometry of the entire product. -/
theorem product_isometry_of_equal_triple_energies
    (rh : IsRound h c) (rg : IsRound g c)
    (ch : IsClosedPlaneSystem h planes) (cg : IsClosedPlaneSystem g planes)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (eq : EqualPlaneTripleEnergies h g planes c t t) :
    ∃ R : V ≃ₗᵢ[ℝ] V, ∀ x y : V, g.L x y = R (h.L x y) := by
  choose r hr using fun i =>
    twoPlane_product_output_isometry (restriction_isRound rh ch i)
      (restriction_isRound rg cg i) (planes.dimension i)
  let T : Module.End ℝ V := ∑ i, ((planes.plane i).subtype.comp (r i).toLinearEquiv.toLinearMap).comp (piP planes i)
  have hT (v : V) : T v = ∑ i, ((r i (piP planes i v) : planes.plane i) : V) := by
    simp [T]
  have hfam : OrthogonalFamily ℝ (fun i => planes.plane i) (fun i => (planes.plane i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise planes.pairwise_orthogonal
  have hn (v : V) : ‖T v‖ = ‖v‖ := by
    have h₁ : ‖T v‖ ^ 2 = ∑ i, ‖r i (piP planes i v)‖ ^ 2 := by
      rw [hT]
      exact hfam.norm_sum (s := Finset.univ) (fun i => r i (piP planes i v))
    have h₂ := hfam.norm_sum (s := Finset.univ) (fun i => piP planes i v)
    change ‖∑ i, planes.proj i v‖ ^ 2 = _ at h₂
    rw [sum_proj_apply] at h₂
    simp only [LinearIsometryEquiv.norm_map] at h₁
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp (h₁.trans h₂.symm)).elim id fun he => by
      linarith [norm_nonneg (T v), norm_nonneg v]
  let Ri : V →ₗᵢ[ℝ] V := ⟨T, hn⟩
  let R : V ≃ₗᵢ[ℝ] V := LinearIsometryEquiv.ofSurjective Ri
    (LinearMap.surjective_of_injective (f := T) Ri.injective)
  have hR (v : V) : R v = ∑ i, ((r i (piP planes i v) : planes.plane i) : V) := hT v
  have refl (i : ι) (u : planes.plane i) : R (u : V) = ((r i u : planes.plane i) : V) := by
    rw [hR, Finset.sum_eq_single i]
    · exact congrArg (fun x => ((r i x : planes.plane i) : V))
        (LinearMap.congr_fun (piP_subtype planes i) u)
    · intro j _ hji
      have he := LinearMap.congr_fun (piP_subtype_ne planes hji) u
      change piP planes j (u : V) = 0 at he
      rw [he, map_zero]
      rfl
    · intro h
      exact (h (Finset.mem_univ i)).elim
  have on_plane (i : ι) (x y : planes.plane i) : g.L (x : V) y = R (h.L (x : V) y) := by
    have hv := congrArg Subtype.val (hr i x y)
    change ((planes.restriction i g).L x y : V) = ((r i ((planes.restriction i h).L x y)) : V) at hv
    rw [← refl] at hv
    change ((g.pullback (planes.plane i).subtype).L x y : V) =
      R (((h.pullback (planes.plane i).subtype).L x y) : V) at hv
    rw [closedSubspace_restriction_product (cg i), closedSubspace_restriction_product (ch i)] at hv
    exact hv
  have mixed (j k : ι) (hjk : j ≠ k) (x : planes.plane j) (y : planes.plane k) :
      g.L (x : V) y = R (h.L (x : V) y) := by
    have component (i : ι) :
        piP planes i (g.L (x : V) y) = r i (piP planes i (h.L (x : V) y)) := by
      by_cases hij : i = j
      · subst i
        rw [(projection_mixed_eq_zero rg cg hjk x y).1, (projection_mixed_eq_zero rh ch hjk x y).1, map_zero]
      by_cases hik : i = k
      · subst i
        rw [(projection_mixed_eq_zero rg cg hjk x y).2, (projection_mixed_eq_zero rh ch hjk x y).2, map_zero]
      · apply ext_inner_left ℝ
        intro v
        obtain ⟨w, rfl⟩ := (r i).surjective v
        obtain ⟨u, hu⟩ := (planeSquareModel rh ch i).2.1 w
        have h' : g.L (u : V) u = ((r i w : planes.plane i) : V) := by
          rw [on_plane i, hu, refl]
        rw [(r i).inner_map_map, inner_piP_left, inner_piP_left]
        have he := planeResponseForms_equal rh rg ch cg eq hij hik hjk u u x y
        unfold planeResponseForm at he
        have hscale : 4 * t * (1 - t) / c ≠ 0 :=
          div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ht₀) (sub_ne_zero.mpr ht₁.symm)) rh.positive.ne'
        have hinner := mul_left_cancel₀ hscale he
        rw [hu, h'] at hinner
        exact hinner.symm
    rw [hR, ← sum_proj_apply planes (g.L (x : V) y)]
    exact Finset.sum_congr rfl fun i _ => congrArg Subtype.val (component i)
  refine ⟨R, fun x y => ?_⟩
  conv_lhs => rw [← sum_proj_apply planes x, ← sum_proj_apply planes y]
  conv_rhs => rw [← sum_proj_apply planes x, ← sum_proj_apply planes y]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst j
    exact on_plane i (piP planes i x) (piP planes i y)
  · exact mixed j i (Ne.symm hij) (piP planes j x) (piP planes i y)

/-- The full labeled assertion of the energy recovery theorem (i), with the same actual sign on
the round cubic and on its pencil value. -/
theorem planePencil_labeled_recovery (rh : IsRound h c) (rg : IsRound g c)
    (ch : IsClosedPlaneSystem h planes) (cg : IsClosedPlaneSystem g planes)
    (m : 1 < Fintype.card ι) {s : ℝ} (eq : EqualPlaneTripleEnergies h g planes c t s) :
    t = s ∧ (t ≠ 0 → t ≠ 1 →
      (g = h ∧ interactionCubic (planePencil g planes) s = interactionCubic (planePencil h planes) t) ∨
      (g = -h ∧ interactionCubic (planePencil g planes) s = -interactionCubic (planePencil h planes) t)) := by
  have he := planePencil_parameter_eq_of_triple_energies rh rg ch cg m eq
  refine ⟨he, ?_⟩
  subst s
  intro ht₀ ht₁
  obtain ⟨R, hR⟩ := product_isometry_of_equal_triple_energies rh rg ch cg ht₀ ht₁ eq
  have hn := Peirce.finrank_eq_twice_card planes
  rcases roundCubic_eq_sign_of_product_isometry rh rg (traceFree_of_isClosedPlaneSystem rh ch)
    (traceFree_of_isClosedPlaneSystem rg cg) (by omega) R hR with heq | heq
  · exact Or.inl ⟨heq, by rw [heq]⟩
  · refine Or.inr ⟨heq, ?_⟩
    rw [heq]
    apply SymmetricCubic.ext
    intro x y z
    have hneg (q : SymmetricCubic V) (u v w : V) : (-q).apply u v w = -q.apply u v w := by
      rw [← neg_one_smul ℝ q, SymmetricCubic.apply_smul, neg_one_mul]
    simp only [hneg, interactionCubic_planePencil_apply, Finset.sum_neg_distrib]
    ring

end
end ThirteenPlanes.RoundCubics
