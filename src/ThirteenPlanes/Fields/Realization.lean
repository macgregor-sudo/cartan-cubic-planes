module

public import ThirteenPlanes.Fields.Classification
public import ThirteenPlanes.ClosedBlocks.Transport
public import ThirteenPlanes.AlbertFlow
public import ThirteenPlanes.Graded.Incidence

@[expose] public section

set_option backward.privateInPublic true

/-! Realizing actual orthogonal closed plane systems in the three-field polynomial form. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Fields

noncomputable section

open RoundCubics

private theorem ordered_triple_sum {m : ℕ} (S : Fin m → Fin m → Fin m → ℝ)
    (swap₁₂ : ∀ i j k, S i j k = S j i k) (swap₂₃ : ∀ i j k, S i j k = S i k j) :
    (∑ i, ∑ j, ∑ k, if i ≠ j ∧ k ≠ i ∧ k ≠ j then S i j k else 0) =
      6 * ∑ t : IncreasingTriple m, S t.1.1 t.1.2.1 t.1.2.2 := by
  let A (i j k : Fin m) := if i < j ∧ j < k then S i j k else 0
  have hsix (i j k : Fin m) : (if i ≠ j ∧ k ≠ i ∧ k ≠ j then S i j k else 0) =
      A i j k + A i k j + A j i k + A j k i + A k i j + A k j i := by
    have h₁ := (swap₂₃ i j k).symm
    have h₂ := (swap₁₂ i j k).symm
    have h₃ := (swap₂₃ j i k).symm.trans h₂
    have h₄ := (swap₁₂ i k j).symm.trans h₁
    have h₅ := (swap₁₂ j k i).symm.trans h₃
    simp only [A, h₁, h₂, h₃, h₄, h₅, Fin.lt_def, ne_eq, Fin.ext_iff]
    split_ifs <;> first | omega | ring
  have swapFirst (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F b a d) = ∑ a, ∑ b, ∑ d, F a b d := Finset.sum_comm
  have swapLast (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F a d b) = ∑ a, ∑ b, ∑ d, F a b d :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have cycle (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F b d a) = ∑ a, ∑ b, ∑ d, F a b d := by
    rw [swapFirst (fun a b d => F a d b), swapLast F]
  have cycleTwice (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F d a b) = ∑ a, ∑ b, ∑ d, F a b d := by
    rw [swapLast (fun a b d => F b a d), swapFirst F]
  have reverse (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F d b a) = ∑ a, ∑ b, ∑ d, F a b d := by
    rw [swapFirst (fun a b d => F d a b), cycleTwice F]
  have hsubtype : (∑ i, ∑ j, ∑ k, A i j k) =
      ∑ t : IncreasingTriple m, S t.1.1 t.1.2.1 t.1.2.2 := by
    have ht := Finset.sum_subtype
      (F := (inferInstance : Fintype (IncreasingTriple m)))
      (p := fun t : Fin m × Fin m × Fin m => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
      (Finset.univ.filter (fun t : Fin m × Fin m × Fin m => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      (by intro t; simp) (fun t : Fin m × Fin m × Fin m => S t.1 t.2.1 t.2.2)
    simpa only [A, Finset.sum_filter, Fintype.sum_prod_type] using ht
  simp_rw [hsix]
  simp only [Finset.sum_add_distrib]
  rw [swapLast A, swapFirst A, cycle A, cycleTwice A, reverse A, hsubtype]
  ring

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private def tripleForm (h : SymmetricCubic V) (i j k : ℂ →ₗ[ℝ] V) : RealTrilinear :=
  LinearMap.mk₂ ℝ (fun x y => (6 : ℝ) • ((innerSL ℝ (h.L (i x) (j y))).toLinearMap.comp k))
    (by
      intro x x' y
      apply LinearMap.ext
      intro w
      change (6 : ℝ) * h.apply (i (x + x')) (j y) (k w) = _
      simp only [map_add, SymmetricCubic.apply_add₁, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
      change 6 * (h.apply (i x) (j y) (k w) + h.apply (i x') (j y) (k w)) =
        6 * h.apply (i x) (j y) (k w) + 6 * h.apply (i x') (j y) (k w)
      ring)
    (by
      intro c x y
      apply LinearMap.ext
      intro w
      change (6 : ℝ) * h.apply (i (c • x)) (j y) (k w) = c * (6 * h.apply (i x) (j y) (k w))
      rw [i.map_smul, SymmetricCubic.apply_smul₁]
      ring)
    (by
      intro x y y'
      apply LinearMap.ext
      intro w
      change (6 : ℝ) * h.apply (i x) (j (y + y')) (k w) =
        6 * h.apply (i x) (j y) (k w) + 6 * h.apply (i x) (j y') (k w)
      rw [j.map_add, SymmetricCubic.apply_add₂]
      ring)
    (by
      intro c x y
      apply LinearMap.ext
      intro w
      change (6 : ℝ) * h.apply (i x) (j (c • y)) (k w) = c * (6 * h.apply (i x) (j y) (k w))
      rw [j.map_smul, SymmetricCubic.apply_smul₂]
      ring)

omit [FiniteDimensional ℝ V] in
private theorem tripleForm_apply (h : SymmetricCubic V) (i j k : ℂ →ₗ[ℝ] V) (x y z : ℂ) :
    tripleForm h i j k x y z = 6 * h.apply (i x) (j y) (k z) := rfl

/-- Any normalized closed plane system is realized by genuine complex fields and
real trilinear terms with three distinct field indices. -/
theorem realization_of_closedPlanes {m : ℕ} {h : SymmetricCubic V} {P : PlaneDecomposition V (Fin m)}
    (round : IsRound h 1) (closed : IsClosedPlaneSystem h P) :
    ∃ I : FieldSpace m ≃ₗᵢ[ℝ] V,
      let g := h.pullback I.toLinearMap
      HasFieldForm g ∧ IsRound g 1 := by
  choose z hz using fun i => (binaryPlaneNormalForm (restriction_isRound round closed i) (P.dimension i)).2
  let emb (i : Fin m) : ℂ →ₗ[ℝ] V := (P.plane i).subtype.comp (z i).symm.toLinearMap
  have he (i : Fin m) (x : ℂ) : emb i x ∈ P.plane i := ((z i).symm x).property
  have horth : OrthogonalFamily ℝ (fun i => P.plane i) (fun i => (P.plane i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise P.pairwise_orthogonal
  have hsum : DirectSum.IsInternal P.plane := horth.isInternal_iff.mpr (by simp [P.exhaustive])
  let E := LinearIsometryEquiv.piLpCongrRight 2 (fun i => (z i).symm)
  let I := E.trans (hsum.isometryL2OfOrthogonalFamily horth).symm
  refine ⟨I, ?_, ?_⟩
  · let T (t : IncreasingTriple m) := tripleForm h (emb t.1.1) (emb t.1.2.1) (emb t.1.2.2)
    refine ⟨T, fun w => ?_⟩
    let v (i : Fin m) := emb i (w i)
    let S (i j k : Fin m) := h.apply (v i) (v j) (v k)
    have hiw : I w = ∑ i, v i := by
      show (hsum.isometryL2OfOrthogonalFamily horth).symm (E w) = _
      rw [DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply]
      rfl
    have hx : h.apply (I w) (I w) (I w) = ∑ i, ∑ j, ∑ k, S i j k := by
      simp only [hiw, S, SymmetricCubic.apply, map_sum, LinearMap.sum_apply, sum_inner, inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      change h.apply (v i) (v j) (v k) = h.apply (v k) (v j) (v i)
      exact (h.apply_swap₁₂ _ _ _).trans ((h.apply_swap₂₃ _ _ _).trans (h.apply_swap₁₂ _ _ _))
    have hrep (i j : Fin m) (hij : i ≠ j) : S i i j = 0 :=
      (P.pairwise_orthogonal hij).inner_eq (closed i (he i (w i)) (he i (w i))) (he j (w j))
    have hdiag (i : Fin m) : S i i i = ((w i) ^ 3).re := by
      have hh := hz i ((z i).symm (w i))
      rw [PlaneDecomposition.restriction_apply] at hh
      change h.apply ↑((z i).symm (w i)) ↑((z i).symm (w i)) ↑((z i).symm (w i)) = _
      simpa only [Real.sqrt_one, one_mul, LinearIsometryEquiv.apply_symm_apply] using hh
    have hsplit (i j k : Fin m) : S i j k =
        (if i = j ∧ j = k then S i i i else 0) +
          (if i ≠ j ∧ k ≠ i ∧ k ≠ j then S i j k else 0) := by
      by_cases hij : i = j
      · subst j
        by_cases hik : i = k
        · subst k
          simp
        · simp [hik, hrep i k hik]
      · by_cases hki : k = i
        · subst k
          have hz := (h.apply_swap₂₃ (v i) (v j) (v i)).trans (hrep i j hij)
          simp [S, hij, hz]
        · by_cases hkj : k = j
          · subst k
            have hz := (h.apply_swap₁₂ (v i) (v j) (v j)).trans
              ((h.apply_swap₂₃ (v j) (v i) (v j)).trans (hrep j i (Ne.symm hij)))
            simp [S, hij, hz]
          · simp [hij, hki, hkj]
    rw [SymmetricCubic.pullback_apply]
    change h.apply (I w) (I w) (I w) = polynomial T w
    rw [hx]
    nth_rw 1 [show (∑ i, ∑ j, ∑ k, S i j k) = ∑ i, ∑ j, ∑ k,
        ((if i = j ∧ j = k then S i i i else 0) +
          (if i ≠ j ∧ k ≠ i ∧ k ≠ j then S i j k else 0)) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hsplit i j k]
    simp only [Finset.sum_add_distrib, ordered_triple_sum S (fun i j k => h.apply_swap₁₂ _ _ _)
      (fun i j k => h.apply_swap₂₃ _ _ _), polynomial, T, tripleForm_apply, ← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [hdiag]
    · intro j _ hji
      simp [hji.symm]
    · simp
  · let g := h.pullback I.toLinearMap
    refine ⟨round.positive, fun u => ?_⟩
    have hp := Peirce.pullback_intertwines_product I (h := g) (k := h) rfl u u
    change I (g.squareMap u) = h.squareMap (I u) at hp
    rw [← I.norm_map (g.squareMap u), hp, round.square_norm, I.norm_map]

end

/-- Every normalized field cubic has radial real-gradient energy. -/
theorem radial_gradient_of_round {m : ℕ} {h : SymmetricCubic (FieldSpace m)} (round : IsRound h 1) :
    ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
      ‖gradient (fun z => h.apply z z z) x‖ = ‖gradient (fun z => h.apply z z z) y‖ := by
  intro x y hxy
  rw [(field_hasGradientAt h x).gradient, (field_hasGradientAt h y).gradient, norm_smul, norm_smul]
  congr 1
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [round.square_norm, round.square_norm, hxy]

/-- Both proper field numbers in Theorem 6-fields are realized on the actual complex and Albert models. -/
theorem four_and_thirteen_field_realizations :
    (∃ h : SymmetricCubic (FieldSpace 4), HasFieldForm h ∧ IsRound h 1) ∧
    (∃ h : SymmetricCubic (FieldSpace 13), HasFieldForm h ∧ IsRound h 1) := by
  constructor
  · obtain ⟨g, gr, _, gc⟩ := PencilEnergy.fourPlane_roundWitness 1 (by norm_num)
    obtain ⟨I, hg⟩ := realization_of_closedPlanes gr gc
    exact ⟨_, hg⟩
  · let code := Graded.nativeCode
    have gr := unitNormalize_isRound nativeEqualCubic_isRound
    have gc : IsClosedPlaneSystem (unitNormalize nativeEqualCubic (1 / 6)) code.decomposition := by
      intro i
      exact (isClosedPiece_smul_iff (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 6)).ne')
        (code.decomposition.plane i)).mpr (code.closedPlaneSystem i)
    obtain ⟨I, hg⟩ := realization_of_closedPlanes gr gc
    exact ⟨_, hg⟩

end

end ThirteenPlanes.Fields
