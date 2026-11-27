module

public import ThirteenPlanes.Peirce.UnitIdempotent
public import ThirteenPlanes.RoundContractions
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true

/-! Complex coordinate planes and the real three-field trilinear interaction. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Fields

noncomputable section

/-- The actual real Hilbert product of `m` complex field coordinates. -/
abbrev FieldSpace (m : ℕ) := PiLp 2 (fun _ : Fin m => ℂ)

abbrev IncreasingTriple (m : ℕ) := {t : Fin m × Fin m × Fin m // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

abbrev RealTrilinear := ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ

/-- Coordinate insertion in the actual field Hilbert space. -/
def axis {m : ℕ} (i : Fin m) : ℂ →ₗᵢ[ℝ] FieldSpace m where
  toLinearMap :=
    { toFun := PiLp.single 2 (β := fun _ : Fin m => ℂ) i
      map_add' a b := by simp [PiLp.single_add]
      map_smul' r a := by
        ext j
        simp [PiLp.single_apply, smul_ite] }
  norm_map' := PiLp.norm_single 2 (fun _ : Fin m => ℂ) i

@[simp] theorem axis_apply {m : ℕ} (i j : Fin m) (z : ℂ) : axis i z j = if i = j then z else 0 := by
  change PiLp.single 2 (β := fun _ : Fin m => ℂ) i z j = _
  by_cases h : i = j <;> simp [h, Ne.symm]

private theorem sum_axis {m : ℕ} (x : FieldSpace m) : (∑ i : Fin m, axis i (x i)) = x := by
  apply PiLp.ext
  intro i
  change ((WithLp.linearEquiv 2 ℝ (Fin m → ℂ)) (∑ j, axis j (x j))) i = x i
  rw [map_sum, Finset.sum_apply]
  simp [axis_apply]

/-- The exhaustive orthogonal system of coordinate two-planes. -/
def coordinatePlanes (m : ℕ) : PlaneDecomposition (FieldSpace m) (Fin m) where
  plane i := (axis i).toLinearMap.range
  dimension i := by
    rw [LinearMap.finrank_range_of_inj (axis i).injective, Complex.finrank_real_complex]
  pairwise_orthogonal := by
    intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    change ⟪axis i z, axis j w⟫ = 0
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      simp [hij.symm]
    · simp [hik]
  exhaustive := by
    rw [eq_top_iff]
    intro x _
    rw [← sum_axis x]
    exact Submodule.sum_mem _ (fun i _ => (le_iSup (fun j => (axis j).toLinearMap.range) i) ⟨x i, rfl⟩)

/-- The exact polynomial from the prescribed single-field and distinct three-field terms. -/
def polynomial {m : ℕ} (T : IncreasingTriple m → RealTrilinear) (z : FieldSpace m) : ℝ :=
  (∑ i, ((z i) ^ 3).re) + ∑ t, T t (z t.1.1) (z t.1.2.1) (z t.1.2.2)

/-- The actual symmetric cubic representing the prescribed field polynomial. -/
def HasFieldForm {m : ℕ} (h : SymmetricCubic (FieldSpace m)) : Prop :=
  ∃ T : IncreasingTriple m → RealTrilinear, ∀ z, h.apply z z z = polynomial T z

private theorem triple_vanishes_on_two_axes {m : ℕ} (T : IncreasingTriple m → RealTrilinear)
    (i j : Fin m) (x : FieldSpace m) (hx : ∀ k, k ≠ i → k ≠ j → x k = 0) :
    (∑ t : IncreasingTriple m, T t (x t.1.1) (x t.1.2.1) (x t.1.2.2)) = 0 := by
  apply Finset.sum_eq_zero
  rintro ⟨⟨a,b,d⟩, hab,hbd⟩ _
  change a < b at hab
  change b < d at hbd
  by_cases ha : a = i ∨ a = j
  · by_cases hb : b = i ∨ b = j
    · have hd : d ≠ i ∧ d ≠ j := by
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
      rw [hx d hd.1 hd.2, map_zero]
    · rw [hx b (fun e => hb (Or.inl e)) (fun e => hb (Or.inr e)), map_zero, LinearMap.zero_apply]
  · rw [hx a (fun e => ha (Or.inl e)) (fun e => ha (Or.inr e)), map_zero,
      LinearMap.zero_apply, LinearMap.zero_apply]

private theorem fieldForm_axis {m : ℕ} (h : SymmetricCubic (FieldSpace m)) (hh : HasFieldForm h)
    (i : Fin m) (z : ℂ) : h.apply (axis i z) (axis i z) (axis i z) = (z ^ 3).re := by
  obtain ⟨T, hT⟩ := hh
  rw [hT, polynomial, triple_vanishes_on_two_axes T i i _ (by
    intro k hk _; simp [hk.symm]), add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · simp

private theorem fieldForm_two_axes {m : ℕ} (h : SymmetricCubic (FieldSpace m)) (hh : HasFieldForm h)
    {i j : Fin m} (hij : i ≠ j) (z w : ℂ) :
    let v := axis i z + axis j w
    h.apply v v v = (z ^ 3).re + (w ^ 3).re := by
  obtain ⟨T, hT⟩ := hh
  dsimp only
  rw [hT, polynomial, triple_vanishes_on_two_axes T i j _ (by
    intro k hki hkj
    change axis i z k + axis j w k = 0
    simp [hki.symm, hkj.symm]), add_zero]
  refine (Finset.sum_subset (s₁ := {i,j}) (s₂ := Finset.univ) (by simp) ?_).symm.trans ?_
  · intro k _ hk
    have hki : k ≠ i := fun e => hk (by simp [e])
    have hkj : k ≠ j := fun e => hk (by simp [e])
    change ((axis i z k + axis j w k) ^ 3).re = 0
    simp [hki.symm, hkj.symm]
  · rw [Finset.sum_pair hij]
    change ((axis i z i + axis j w i) ^ 3).re + ((axis i z j + axis j w j) ^ 3).re = _
    simp [hij, hij.symm]

private theorem diagonal_odd_polarize {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (h : SymmetricCubic V) (x y : V) :
    6 * h.apply x x y = h.apply (x+y) (x+y) (x+y) - h.apply (x-y) (x-y) (x-y) - 2 * h.apply y y y := by
  rw [show x - y = x + (-1 : ℝ) • y by rw [neg_one_smul, sub_eq_add_neg]]
  have hs := h.apply_swap₂₃ x y x
  have ht := (h.apply_swap₁₂ y x x).trans hs
  simp only [SymmetricCubic.apply_add₁, SymmetricCubic.apply_add₂, SymmetricCubic.apply_add₃,
    SymmetricCubic.apply_smul₁, SymmetricCubic.apply_smul₂, SymmetricCubic.apply_smul₃, hs, ht]
  ring

private theorem two_axis_cubic_zero {m : ℕ} (h : SymmetricCubic (FieldSpace m)) (hh : HasFieldForm h)
    {i j : Fin m} (hij : i ≠ j) (z w t : ℂ) : h.apply (axis i z) (axis i w) (axis j t) = 0 := by
  have dsq (u : ℂ) : h.apply (axis i u) (axis i u) (axis j t) = 0 := by
    have hp := diagonal_odd_polarize h (axis i u) (axis j t)
    have hsub : axis i u - axis j t = axis i u + axis j (-t) := by
      rw [(axis j).map_neg, sub_eq_add_neg]
    rw [hsub, fieldForm_two_axes h hh hij,
      fieldForm_two_axes h hh hij, fieldForm_axis h hh] at hp
    have hneg : (((-t) ^ 3 : ℂ)).re = -((t ^ 3 : ℂ)).re := by
      rw [show (-t) ^ 3 = -(t ^ 3) by ring, Complex.neg_re]
    rw [hneg] at hp
    linarith only [hp]
  have hs := dsq (z + w)
  rw [map_add] at hs
  simp only [SymmetricCubic.apply_add₁, SymmetricCubic.apply_add₂, dsq,
    h.apply_swap₁₂ (axis i w) (axis i z), zero_add, add_zero] at hs
  linarith only [hs]

private theorem inner_axis_right {m : ℕ} (x : FieldSpace m) (i : Fin m) (z : ℂ) :
    ⟪x, axis i z⟫ = ⟪x i, z⟫ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · simp

/-- An actual three-field polynomial makes the coordinate planes closed. -/
theorem fieldForm_coordinatePlanes_closed {m : ℕ} (h : SymmetricCubic (FieldSpace m)) (hh : HasFieldForm h) :
    IsClosedPlaneSystem h (coordinatePlanes m) := by
  intro i
  rintro _ _ ⟨z, rfl⟩ ⟨w, rfl⟩
  let a := h.L (axis i z) (axis i w)
  refine ⟨a i, ?_⟩
  change axis i (a i) = a
  apply PiLp.ext
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · have hp := two_axis_cubic_zero h hh hij z w (a j)
    change ⟪a, axis j (a j)⟫ = 0 at hp
    rw [inner_axis_right, real_inner_self_eq_norm_sq] at hp
    rw [axis_apply, ite_eq_right hij]
    exact (norm_eq_zero.mp (sq_eq_zero_iff.mp hp)).symm

private theorem axis_one_square {m : ℕ} (h : SymmetricCubic (FieldSpace m)) (hh : HasFieldForm h) (i : Fin m) :
    h.squareMap (axis i 1) = axis i 1 := by
  let a := axis i 1
  have ha : a ∈ (coordinatePlanes m).plane i := ⟨1, rfl⟩
  have hc := fieldForm_coordinatePlanes_closed h hh i ha ha
  obtain ⟨w, hw⟩ := hc
  change axis i w = h.squareMap a at hw
  have htest (z : ℂ) : h.apply a a (axis i z) = z.re := by
    have hp := diagonal_odd_polarize h a (axis i z)
    change 6 * h.apply a a (axis i z) = _ at hp
    dsimp only [a] at hp
    rw [← map_add, ← map_sub, fieldForm_axis h hh, fieldForm_axis h hh, fieldForm_axis h hh] at hp
    have hpoly := congrArg Complex.re (show (1+z)^3 - (1-z)^3 - 2*z^3 = 6*z by ring)
    norm_num [Complex.sub_re, Complex.mul_re] at hpoly
    linarith only [hp, hpoly]
  suffices w = 1 from by rw [← hw, this]
  apply ext_inner_right ℝ
  intro z
  have hz := htest z
  change ⟪h.squareMap a, axis i z⟫ = z.re at hz
  rw [← hw, (axis i).inner_map_map] at hz
  rw [hz]
  simp [Complex.inner]

/-- The true real gradient of `W(z)=d(z,z,z)` is three times the cubic square. -/
theorem field_hasGradientAt {m : ℕ} (h : SymmetricCubic (FieldSpace m)) (x : FieldSpace m) :
    HasGradientAt (fun z => h.apply z z z) ((3 : ℝ) • h.squareMap x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := (Peirce.cubic_hasStrictFDerivAt h x).hasFDerivAt
  convert hd using 1
  ext y
  simp [SymmetricCubic.squareMap, InnerProductSpace.toDual_apply_apply,
    smul_eq_mul]

/-- Lemma 6-fields. Radial length of the real gradient fixes the round strength to one. -/
theorem fieldForm_round_of_radial_gradient {m : ℕ} (hm : 1 ≤ m) (h : SymmetricCubic (FieldSpace m))
    (hh : HasFieldForm h)
    (radial : ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
      ‖gradient (fun z => h.apply z z z) x‖ = ‖gradient (fun z => h.apply z z z) y‖) :
    IsRound h 1 ∧ h.TraceFree ∧ IsClosedPlaneSystem h (coordinatePlanes m) := by
  have hc := fieldForm_coordinatePlanes_closed h hh
  let u := axis (⟨0, by omega⟩ : Fin m) 1
  have hu : ‖u‖ = 1 := by simp [u]
  have hs : h.squareMap u = u := axis_one_square h hh _
  have hr : IsRound h 1 := by
    refine ⟨by norm_num, fun x => ?_⟩
    have hn : ‖x‖ = ‖‖x‖ • u‖ := by simp [norm_smul, hu]
    have hy := radial x (‖x‖ • u) hn
    have hsq : h.squareMap (‖x‖ • u) = ‖x‖ ^ 2 • h.squareMap u := by
      simp [SymmetricCubic.squareMap, pow_two, smul_smul]
    rw [(field_hasGradientAt h x).gradient, (field_hasGradientAt h (‖x‖ • u)).gradient, hsq, hs] at hy
    simp only [norm_smul, Real.norm_of_nonneg (sq_nonneg ‖x‖), hu, mul_one] at hy
    have hnorm : ‖h.squareMap x‖ = ‖x‖ ^ 2 := by
      norm_num at hy
      linarith only [hy]
    rw [hnorm, ← pow_mul]
    norm_num
  exact ⟨hr, RoundCubics.traceFree_of_isClosedPlaneSystem hr hc, hc⟩

end

end ThirteenPlanes.Fields
