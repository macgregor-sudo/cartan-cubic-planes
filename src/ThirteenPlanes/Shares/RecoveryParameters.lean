module

public import ThirteenPlanes.Shares.Responses

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {h g : SymmetricCubic V} {planes : PlaneDecomposition V ι} {c t s : ℝ}

/-- Equality of the energies on each sum of three distinct labeled planes. -/
def EqualPlaneTripleEnergies (h g : SymmetricCubic V) (planes : PlaneDecomposition V ι)
    (c t s : ℝ) : Prop :=
  ∀ (i j k : ι), i ≠ j → i ≠ k → j ≠ k → ∀ x : V,
    x ∈ (planes.plane i ⊔ planes.plane j) ⊔ planes.plane k →
      normalizedPencilEnergy h planes c t x = normalizedPencilEnergy g planes c s x

private theorem quarticResponse_equal (eq : EqualPlaneTripleEnergies h g planes c t s)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : planes.plane i) (y : planes.plane j) (z : planes.plane k) :
    quarticResponse (normalizedPencilEnergy h planes c t) (u : V) y z =
      quarticResponse (normalizedPencilEnergy g planes c s) (u : V) y z := by
  let O := (planes.plane i ⊔ planes.plane j) ⊔ planes.plane k
  have h₁ : planes.plane i ≤ O := le_sup_left.trans le_sup_left
  have h₂ : planes.plane j ≤ O := le_sup_right.trans le_sup_left
  have h₃ : planes.plane k ≤ O := le_sup_right
  have e (u : planes.plane i) (y : planes.plane j) (z : planes.plane k) :
      normalizedPencilEnergy h planes c t ((u : V) + y + z) =
        normalizedPencilEnergy g planes c s ((u : V) + y + z) :=
    eq i j k hij hik hjk _ (O.add_mem (O.add_mem (h₁ u.property) (h₂ y.property)) (h₃ z.property))
  have e0 (y : planes.plane j) (z : planes.plane k) :
      normalizedPencilEnergy h planes c t ((y : V) + z) =
        normalizedPencilEnergy g planes c s ((y : V) + z) :=
    eq i j k hij hik hjk _ (O.add_mem (h₂ y.property) (h₃ z.property))
  have en₁ := e u y (-z)
  have en₂ := e u (-y) z
  have en₃ := e u (-y) (-z)
  have en₄ := e0 y (-z)
  have en₅ := e0 (-y) z
  have en₆ := e0 (-y) (-z)
  simp only [Submodule.coe_neg] at en₁ en₂ en₃ en₄ en₅ en₆
  simp only [quarticResponse, e u y z, en₁, en₂, en₃, e0 y z, en₄, en₅, en₆]

/-- The actual polarized response forms are equal whenever the labeled triple energies are equal. -/
theorem planeResponseForms_equal (rh : IsRound h c) (rg : IsRound g c)
    (ch : IsClosedPlaneSystem h planes) (cg : IsClosedPlaneSystem g planes)
    (eq : EqualPlaneTripleEnergies h g planes c t s)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u u' : planes.plane i) (y : planes.plane j) (z : planes.plane k) :
    planeResponseForm h c t (u : V) u' y z = planeResponseForm g c s (u : V) u' y z := by
  rw [planeResponseForm_eq_quartic_polarization rh ch t hij hik hjk,
    planeResponseForm_eq_quartic_polarization rg cg s hij hik hjk,
    quarticResponse_equal eq hij hik hjk (u + u') y z,
    quarticResponse_equal eq hij hik hjk u y z, quarticResponse_equal eq hij hik hjk u' y z]

/-- The energy at the sum of two orthogonal unit fields is twice one plus twice the
squared mixing parameter. -/
theorem normalizedPencilEnergy_two_units (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (t : ℝ) {i j : ι} (hij : i ≠ j) (x : planes.plane i) (y : planes.plane j)
    (hx : ‖(x : V)‖ = 1) (hy : ‖(y : V)‖ = 1) :
    normalizedPencilEnergy h planes c t ((x : V) + y) = 2 + 2 * t ^ 2 := by
  let p := interactionCubic (planePencil h planes) t
  have hp : p.squareMap ((x : V) + y) =
      (h.L (x : V) x + h.L (y : V) y) + (2 * t) • h.L (x : V) y := by
    change p.L ((x : V) + y) ((x : V) + y) = _
    simp only [map_add, LinearMap.add_apply, p, pencil_product_same closed t i x x,
      pencil_product_same closed t j y y, pencil_product_distinct t hij x y,
      pencil_product_distinct t hij.symm y x, h.L_comm (y : V) (x : V)]
    module
  have hi := closed i x.property x.property
  have hj := closed j y.property y.property
  obtain ⟨hm, hn⟩ := (mixedProductLaw round (planes.pairwise_orthogonal hij)
    (closed i) (closed j)).1 x.property y.property
  have ho : ⟪h.L (x : V) x, h.L (y : V) y⟫ = 0 := (planes.pairwise_orthogonal hij).inner_eq hi hj
  have ho' : ⟪h.L (x : V) x + h.L (y : V) y, (2 * t) • h.L (x : V) y⟫ = 0 := by
    rw [real_inner_smul_right, Submodule.inner_right_of_mem_orthogonal
      ((planes.plane i ⊔ planes.plane j).add_mem
        ((show planes.plane i ≤ planes.plane i ⊔ planes.plane j from le_sup_left) hi)
        ((show planes.plane j ≤ planes.plane i ⊔ planes.plane j from le_sup_right) hj)) hm, mul_zero]
  have n₁ : ‖h.L (x : V) x‖ ^ 2 = c := by simpa [SymmetricCubic.squareMap, hx] using round.square_norm (x : V)
  have n₂ : ‖h.L (y : V) y‖ ^ 2 = c := by simpa [SymmetricCubic.squareMap, hy] using round.square_norm (y : V)
  have n₁₂ : ‖h.L (x : V) y‖ ^ 2 = c / 2 := by
    rw [hx, hy] at hn
    linarith
  change ‖p.squareMap ((x : V) + y)‖ ^ 2 / c = _
  rw [hp, norm_add_sq_real _ _, ho', norm_add_sq_real (h.L (x : V) x) (h.L (y : V) y),
    ho, n₁, n₂, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, n₁₂]
  field_simp [round.positive.ne']
  ring

private theorem response_norm_pair_sum (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (e : (i : ι) → OrthonormalBasis (Fin 2) ℝ (planes.plane i))
    (t : ℝ) {j k : ι} (hjk : j ≠ k) :
    (∑ i ∈ Finset.univ.filter (fun i => i ≠ j ∧ i ≠ k),
      planeResponseNormSq h planes e c t i j k) = 64 * t ^ 2 * (1 - t) ^ 2 := by
  have h (i : ι) (hi : i ∈ Finset.univ.filter (fun i => i ≠ j ∧ i ≠ k)) :
      planeResponseNormSq h planes e c t i j k =
        32 * t ^ 2 * (1 - t) ^ 2 * planeShare h planes j k i := by
    have hij := (Finset.mem_filter.mp hi).2.1
    rw [planeResponseNormSq_eq_share round closed e t hij hjk,
      planeShare_cycle round closed hij hjk]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, planeShare_pair_sum round closed hjk]
  ring

/-- The signed parameter in energy recovery theorem (i), determined even at zero and one. -/
theorem planePencil_parameter_eq_of_triple_energies (rh : IsRound h c) (rg : IsRound g c)
    (ch : IsClosedPlaneSystem h planes) (cg : IsClosedPlaneSystem g planes)
    (m : 1 < Fintype.card ι) (eq : EqualPlaneTripleEnergies h g planes c t s) : t = s := by
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp m
  obtain ⟨j, k, hjk⟩ := exists_pair_ne ι
  let C := Finset.univ.filter (fun i => i ≠ j ∧ i ≠ k)
  have hC : C.Nonempty := by
    by_contra hn
    have hz := planeShare_pair_sum rh ch hjk
    change (∑ i ∈ C, _) = 2 at hz
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hz
    norm_num at hz
  obtain ⟨i, hi⟩ := hC
  have hij := (Finset.mem_filter.mp hi).2.1
  have hik := (Finset.mem_filter.mp hi).2.2
  let e (l : ι) := (stdOrthonormalBasis ℝ (planes.plane l)).reindex (finCongr (planes.dimension l))
  let O := (planes.plane i ⊔ planes.plane j) ⊔ planes.plane k
  have hj : planes.plane j ≤ O := le_sup_right.trans le_sup_left
  have hk : planes.plane k ≤ O := le_sup_right
  have he := eq i j k hij hik hjk ((e j 0 : V) + e k 0)
    (O.add_mem (hj (e j 0).property) (hk (e k 0).property))
  rw [normalizedPencilEnergy_two_units rh ch t hjk (e j 0) (e k 0)
    ((e j).orthonormal.norm_eq_one 0) ((e k).orthonormal.norm_eq_one 0),
    normalizedPencilEnergy_two_units rg cg s hjk (e j 0) (e k 0)
      ((e j).orthonormal.norm_eq_one 0) ((e k).orthonormal.norm_eq_one 0)] at he
  have ht2 : t ^ 2 = s ^ 2 := by linarith
  have hform (i : ι) (hi : i ∈ C) :
      planeResponseNormSq h planes e c t i j k = planeResponseNormSq g planes e c s i j k := by
    have hij := (Finset.mem_filter.mp hi).2.1
    have hik := (Finset.mem_filter.mp hi).2.2
    unfold planeResponseNormSq
    simp_rw [planeResponseForms_equal rh rg ch cg eq hij hik hjk]
  have hs := Finset.sum_congr rfl hform
  rw [response_norm_pair_sum rh ch e t hjk, response_norm_pair_sum rg cg e s hjk] at hs
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht2 with heq | heq
  · exact heq
  · by_cases ht : t = 0
    · linarith
    have hz : (1 - t) ^ 2 = (1 - s) ^ 2 := by
      refine mul_left_cancel₀ (mul_ne_zero (by norm_num : (64 : ℝ) ≠ 0) (pow_ne_zero 2 ht)) ?_
      rwa [← ht2] at hs
    rw [heq] at hz
    nlinarith

end
end ThirteenPlanes.RoundCubics
