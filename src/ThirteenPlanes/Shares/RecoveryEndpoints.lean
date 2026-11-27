module

public import ThirteenPlanes.Shares.PlaneTransport
public import ThirteenPlanes.PlanePencilSplit
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace
open PlaneContractions

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {h : SymmetricCubic V} {planes : PlaneDecomposition V ι} {c : ℝ}

theorem normalizedPencilEnergy_zero (round : IsRound h c) (closed : IsClosedPlaneSystem h planes) (x : V) :
    normalizedPencilEnergy h planes c 0 x = ∑ i, ‖planes.proj i x‖ ^ 4 := by
  let y (i : ι) : planes.plane i :=
    ⟨h.L (planes.proj i x) (planes.proj i x),
      closed i (piP planes i x).property (piP planes i x).property⟩
  have hfam : OrthogonalFamily ℝ (fun i => planes.plane i) (fun i => (planes.plane i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise planes.pairwise_orthogonal
  have hdiag : interactionCubic (planePencil h planes) 0 = (planePencil h planes).diagonalCubic := by
    simp [interactionCubic]
  unfold normalizedPencilEnergy
  rw [hdiag, planePencil_diagonal_sq closed]
  change ‖∑ i, (planes.plane i).subtypeₗᵢ (y i)‖ ^ 2 / c = _
  rw [hfam.norm_sum]
  have hterm (i : ι) : ‖y i‖ ^ 2 = c * ‖planes.proj i x‖ ^ 4 := round.square_norm (planes.proj i x)
  simp_rw [hterm, ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ round.positive.ne'

theorem normalizedPencilEnergy_one (round : IsRound h c) (x : V) :
    normalizedPencilEnergy h planes c 1 x = ‖x‖ ^ 4 := by
  rw [normalizedPencilEnergy, planePencil_at_one, round.square_norm]
  exact mul_div_cancel_left₀ _ round.positive.ne'

omit [Fintype ι] in
private theorem plane_nonzero_diagonal_cubic (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) (i : ι) : ∃ x : planes.plane i, h.apply (x : V) x x ≠ 0 := by
  obtain ⟨_, z, hz⟩ := binaryPlaneNormalForm (restriction_isRound round closed i) (planes.dimension i)
  let x := z.symm (1 : ℂ)
  refine ⟨x, ?_⟩
  have hx := hz x
  rw [planes.restriction_apply] at hx
  change h.apply (x : V) x x = Real.sqrt c * ((z (z.symm 1)) ^ 3).re at hx
  rw [z.apply_symm_apply] at hx
  norm_num at hx
  rw [hx]
  exact (Real.sqrt_pos.2 round.positive).ne'

theorem pencil_cubic_on_plane (closed : IsClosedPlaneSystem h planes) (t : ℝ)
    (i : ι) (x y z : planes.plane i) :
    (interactionCubic (planePencil h planes) t).apply (x : V) y z = h.apply (x : V) y z := by
  unfold SymmetricCubic.apply
  rw [pencil_product_same closed t i x y]

omit [FiniteDimensional ℝ V] in
theorem cubic_negate_three_inputs (h : SymmetricCubic V) (x y z : V) :
    h.apply (-x) (-y) (-z) = -(h.apply x y z) := by
  simp only [← SymmetricCubic.trilinear_apply, map_neg, LinearMap.neg_apply, neg_neg]

/-- The full endpoint counterexample in energy recovery theorem (ii), using the original complete planes. -/
theorem planePencil_endpoint_nonunique (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) (m : 1 < Fintype.card ι) (t : ℝ)
    (ht : t = 0 ∨ t = 1) :
    ∃ g : SymmetricCubic V, IsRound g c ∧ IsClosedPlaneSystem g planes ∧
      (∀ x : V, normalizedPencilEnergy g planes c t x = normalizedPencilEnergy h planes c t x) ∧
      interactionCubic (planePencil g planes) t ≠ interactionCubic (planePencil h planes) t ∧
      interactionCubic (planePencil g planes) t ≠ -interactionCubic (planePencil h planes) t := by
  classical
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp m
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let I := (planes.plane i)ᗮ.reflection
  let g := h.pullback I.toLinearMap
  have hr : IsRound g c := IsRound.pullback_isometry round I
  have hi (x : V) (hx : x ∈ planes.plane i) : I x = -x :=
    Submodule.reflection_mem_subspace_orthogonal_precomplement_eq_neg hx
  have hj {k : ι} (hk : i ≠ k) (x : V) (hx : x ∈ planes.plane k) : I x = x :=
    Submodule.reflection_mem_subspace_eq_self ((planes.pairwise_orthogonal hk.symm).le hx)
  have leave (k : ι) {x : V} (hx : x ∈ planes.plane k) : I x ∈ planes.plane k := by
    by_cases hk : i = k
    · subst k
      rw [hi _ hx]
      exact (planes.plane i).neg_mem hx
    · rwa [hj hk _ hx]
  have hp : pullbackPlaneSystem planes I = planes := by
    apply planeSystem_eq_of_pointwise
    intro k
    ext x
    rw [mem_pullbackPlaneSystem]
    constructor
    · intro hx
      have hh := leave k hx
      have hinv : I (I x) = x := (planes.plane i)ᗮ.reflection_reflection x
      exact hinv ▸ hh
    · exact leave k
  have gc := IsClosedPlaneSystem.pullback_isometry closed I
  change IsClosedPlaneSystem g (pullbackPlaneSystem planes I) at gc
  rw [hp] at gc
  refine ⟨g, hr, gc, fun x => ?_, ?_, ?_⟩
  · rcases ht with rfl | rfl
    · rw [normalizedPencilEnergy_zero hr gc, normalizedPencilEnergy_zero round closed]
    · rw [normalizedPencilEnergy_one hr, normalizedPencilEnergy_one round]
  · intro eq
    obtain ⟨x, hx⟩ := plane_nonzero_diagonal_cubic round closed i
    have he := congrArg (fun q : SymmetricCubic V => q.apply (x : V) x x) eq
    rw [pencil_cubic_on_plane gc, pencil_cubic_on_plane closed] at he
    change (h.pullback I.toLinearMap).apply (x : V) x x = _ at he
    rw [SymmetricCubic.pullback_apply] at he
    change h.apply (I x) (I x) (I x) = _ at he
    rw [hi x x.property, cubic_negate_three_inputs] at he
    exact hx (by linarith)
  · intro eq
    obtain ⟨x, hx⟩ := plane_nonzero_diagonal_cubic round closed j
    have he := congrArg (fun q : SymmetricCubic V => q.apply (x : V) x x) eq
    rw [pencil_cubic_on_plane gc] at he
    have hneg (q : SymmetricCubic V) : (-q).apply (x : V) x x = -q.apply (x : V) x x := by
      rw [← neg_one_smul ℝ q, SymmetricCubic.apply_smul, neg_one_mul]
    rw [hneg, pencil_cubic_on_plane closed] at he
    change (h.pullback I.toLinearMap).apply (x : V) x x = _ at he
    rw [SymmetricCubic.pullback_apply] at he
    change h.apply (I x) (I x) (I x) = _ at he
    rw [hj hij x x.property] at he
    exact hx (by linarith)

end
end ThirteenPlanes.RoundCubics
