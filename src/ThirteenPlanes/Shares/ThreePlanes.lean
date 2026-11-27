module

public import ThirteenPlanes.PlaneShares

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators InnerProductSpace RealInnerProductSpace TensorProduct

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {c : ℝ} {U U' W : Submodule ℝ V}

/-- The share of the third subspace in the span of products of the first two. -/
def shareOfThreePlanes (h : SymmetricCubic V) (U U' W : Submodule ℝ V) : ℝ :=
  (1 / 2) * LinearMap.trace ℝ V
    (W.starProjection.toLinearMap.comp (mixedProductSpace h U U').starProjection.toLinearMap)

theorem planeShare_eq_shareOfThreePlanes {ι : Type*} (h : SymmetricCubic V)
    (planes : PlaneDecomposition V ι) (i j k : ι) :
    planeShare h planes i j k = shareOfThreePlanes h (planes.plane i) (planes.plane j) (planes.plane k) :=
  rfl

private theorem trace_projection_pair (S T : Submodule ℝ V)
    {α : Type*} [Fintype α] (e : OrthonormalBasis α ℝ S) :
    LinearMap.trace ℝ V (S.starProjection.toLinearMap.comp T.starProjection.toLinearMap) =
      ∑ a, ‖T.starProjection (e a : V)‖ ^ 2 := by
  change LinearMap.trace ℝ V
    ((S.subtype.comp S.orthogonalProjectionOnto.toLinearMap).comp T.starProjection.toLinearMap) = _
  rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm'
    (S.orthogonalProjectionOnto.toLinearMap.comp T.starProjection.toLinearMap) S.subtype,
    SymmetricCubic.trace_eq_sum_inner e]
  refine Finset.sum_congr rfl fun a _ => ?_
  change ⟪e a, S.orthogonalProjectionOnto (T.starProjection (e a : V))⟫ = _
  rw [S.inner_orthogonalProjectionOnto_eq_of_mem_left, real_inner_comm]
  exact T.re_inner_starProjection_eq_normSq (e a : V)

/-- The share is the squared projection mass of the mixed products of orthonormal bases. -/
theorem shareOfThreePlanes_eq_sum_projected_sq (round : IsRound h c)
    (orth : U.IsOrtho U') (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (W : Submodule ℝ V)
    {α β : Type*} [Fintype α] [Fintype β]
    (e : OrthonormalBasis α ℝ U) (f : OrthonormalBasis β ℝ U') :
    shareOfThreePlanes h U U' W =
      (1 / c) * ∑ a, ∑ b, ‖W.starProjection (h.L (e a : V) (f b : V))‖ ^ 2 := by
  let S := mixedProductSpace h U U'
  let s := Real.sqrt (c / 2)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos round.positive (by norm_num))
  let b := (e.tensorProduct f).map (mixedTensorIsometry round orth closed closed' dim)
  have hb (p : α × β) : (b p : V) = s⁻¹ • h.L (e p.1 : V) (f p.2 : V) := by
    simp [b, s, mixedTensorIsometry_apply, OrthonormalBasis.tensorProduct_apply']
  change (1 / 2) * LinearMap.trace ℝ V (W.starProjection.toLinearMap.comp S.starProjection.toLinearMap) = _
  rw [LinearMap.trace_comp_comm' S.starProjection.toLinearMap W.starProjection.toLinearMap,
    trace_projection_pair S W b, Fintype.sum_prod_type]
  simp only [hb, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs),
    mul_pow, ← Finset.mul_sum]
  rw [← mul_assoc]
  congr 1
  change (1 / 2) * ((Real.sqrt (c / 2))⁻¹) ^ 2 = 1 / c
  rw [inv_pow, Real.sq_sqrt (div_nonneg round.positive.le (by norm_num : (0 : ℝ) ≤ 2))]
  field_simp [round.positive.ne']

/-- The coefficient formula in three-plane share identities (i)`, with no complete system of planes. -/
theorem shareOfThreePlanes_eq_sum_cubic_sq (round : IsRound h c)
    (orth : U.IsOrtho U') (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2)
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : OrthonormalBasis α ℝ U) (f : OrthonormalBasis β ℝ U') (g : OrthonormalBasis γ ℝ W) :
    shareOfThreePlanes h U U' W =
      (1 / c) * ∑ a, ∑ b, ∑ d, (h.apply (e a : V) (f b : V) (g d : V)) ^ 2 := by
  rw [shareOfThreePlanes_eq_sum_projected_sq round orth closed closed' dim W e f]
  have hn (v : V) : ‖W.starProjection v‖ ^ 2 = ∑ d, ⟪v, (g d : V)⟫ ^ 2 := by
    change ‖W.orthogonalProjectionOnto v‖ ^ 2 = _
    rw [← g.sum_sq_inner_left]
    simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simp only [hn, SymmetricCubic.apply]

theorem shareOfThreePlanes_swap_first (round : IsRound h c)
    (orth : U.IsOrtho U') (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (dim' : Module.finrank ℝ U' = 2) (W : Submodule ℝ V) :
    shareOfThreePlanes h U U' W = shareOfThreePlanes h U' U W := by
  let e := stdOrthonormalBasis ℝ U
  let f := stdOrthonormalBasis ℝ U'
  let g := stdOrthonormalBasis ℝ W
  rw [shareOfThreePlanes_eq_sum_cubic_sq round orth closed closed' dim e f g,
    shareOfThreePlanes_eq_sum_cubic_sq round orth.symm closed' closed dim' f e g]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun d _ => by rw [h.apply_swap₁₂]

theorem shareOfThreePlanes_swap_last (round : IsRound h c)
    (orth : U.IsOrtho U') (orthW : U.IsOrtho W) (closed : IsClosedPiece h U)
    (closed' : IsClosedPiece h U') (closedW : IsClosedPiece h W)
    (dim : Module.finrank ℝ U = 2) :
    shareOfThreePlanes h U U' W = shareOfThreePlanes h U W U' := by
  let e := stdOrthonormalBasis ℝ U
  let f := stdOrthonormalBasis ℝ U'
  let g := stdOrthonormalBasis ℝ W
  rw [shareOfThreePlanes_eq_sum_cubic_sq round orth closed closed' dim e f g,
    shareOfThreePlanes_eq_sum_cubic_sq round orthW closed closedW dim e g f]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => by rw [h.apply_swap₂₃]

theorem shareOfThreePlanes_cycle (round : IsRound h c)
    (orth : U.IsOrtho U') (orthW : U'.IsOrtho W)
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U') (closedW : IsClosedPiece h W)
    (dim : Module.finrank ℝ U = 2) (dim' : Module.finrank ℝ U' = 2) :
    shareOfThreePlanes h U U' W = shareOfThreePlanes h U' W U :=
  (shareOfThreePlanes_swap_first round orth closed closed' dim dim' W).trans
    (shareOfThreePlanes_swap_last round orth.symm orthW closed' closed closedW dim')

end
end ThirteenPlanes.RoundCubics
