module

public import ThirteenPlanes.Shares.ThreePlanes

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {J : V →ₗᵢ[ℝ] E} {e : E} {S : Submodule ℝ V}

/-- A rank-three trace frame with its associated plane. The points are orthonormal
in the ambient trace metric and sum to the unit. Their centered points span the plane. -/
structure CenteredTraceFrame (J : V →ₗᵢ[ℝ] E) (e : E) (S : Submodule ℝ V) where
  point : Fin 3 → E
  orthonormal : Orthonormal ℝ point
  point_sum : ∑ a, point a = e
  centered : Fin 3 → S
  centered_eq : ∀ a, J (centered a : V) = point a - (1 / 3 : ℝ) • e
  span_centered : Submodule.span ℝ (Set.range centered) = ⊤

namespace CenteredTraceFrame

variable (F : CenteredTraceFrame J e S)

private theorem point_inner_unit (a : Fin 3) : ⟪F.point a, e⟫ = 1 := by
  calc
    _ = ⟪F.point a, ∑ i, F.point i⟫ := congrArg (inner ℝ (F.point a)) F.point_sum.symm
    _ = _ := by simp [inner_sum, orthonormal_iff_ite.mp F.orthonormal]

private theorem unit_inner_point (a : Fin 3) : ⟪e, F.point a⟫ = 1 :=
  (real_inner_comm _ _).trans (F.point_inner_unit a)

theorem unit_inner_self (F : CenteredTraceFrame J e S) : ⟪e, e⟫ = 3 := by
  calc
    _ = ⟪e, ∑ a, F.point a⟫ := congrArg (inner ℝ e) F.point_sum.symm
    _ = _ := by simp [inner_sum, F.unit_inner_point]

theorem centered_inner_unit (a : Fin 3) : ⟪J (F.centered a : V), e⟫ = 0 := by
  rw [F.centered_eq, inner_sub_left, real_inner_smul_left, F.point_inner_unit, F.unit_inner_self]
  norm_num

/-- The Gram matrix of the three centered points. -/
theorem centered_inner (a b : Fin 3) :
    ⟪F.centered a, F.centered b⟫ = (if a = b then (1 : ℝ) else 0) - 1 / 3 := by
  change ⟪(F.centered a : V), (F.centered b : V)⟫ = _
  rw [← J.inner_map_map, F.centered_eq, F.centered_eq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp F.orthonormal, F.point_inner_unit, F.unit_inner_point, F.unit_inner_self]
  ring

private theorem centered_sum : (∑ a, F.centered a) = 0 := by
  apply Subtype.ext
  apply J.injective
  change J ((∑ a, F.centered a : S) : V) = J 0
  simp only [Submodule.coe_sum, map_sum, map_zero, F.centered_eq]
  rw [Finset.sum_sub_distrib, F.point_sum]
  simp only [Fin.sum_univ_three]
  module

/-- Centered points of a rank-three trace frame reconstruct each vector of its plane. -/
theorem reconstruction (x : S) : (∑ a, ⟪F.centered a, x⟫ • F.centered a) = x := by
  let L : Module.End ℝ S :=
    ∑ a, (LinearMap.toSpanSingleton ℝ S (F.centered a)).comp (innerₗ S (F.centered a))
  have hL : L = LinearMap.id := by
    apply LinearMap.ext_on_range F.span_centered
    intro a
    simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.toSpanSingleton_apply]
    change (∑ i, ⟪F.centered i, F.centered a⟫ • F.centered i) = F.centered a
    simp only [F.centered_inner, sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
      F.centered_sum, smul_zero, sub_zero, ite_smul, one_smul, zero_smul]
    simp
  have hx := DFunLike.congr_fun hL x
  simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.toSpanSingleton_apply] at hx
  change (∑ a, ⟪F.centered a, x⟫ • F.centered a) = x at hx
  exact hx

variable [FiniteDimensional ℝ V]

theorem sum_sq_functional {α : Type*} [Fintype α] (L : S →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis α ℝ S) : (∑ a, (L (F.centered a)) ^ 2) = ∑ i, (L (b i)) ^ 2 := by
  let z := SymmetricCubic.riesz L
  have hL (x : S) : L x = ⟪z, x⟫ := (SymmetricCubic.inner_riesz L x).symm
  calc
    _ = ⟪z, ∑ a, ⟪F.centered a, z⟫ • F.centered a⟫ := by
      simp only [inner_sum, real_inner_smul_right, hL]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [real_inner_comm z (F.centered a), pow_two]
    _ = ‖z‖ ^ 2 := by rw [F.reconstruction, real_inner_self_eq_norm_sq]
    _ = _ := by
      rw [← b.sum_sq_inner_left]
      simp only [hL]

end CenteredTraceFrame

variable [FiniteDimensional ℝ V] {U U' W : Submodule ℝ V} {h : SymmetricCubic V}

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem replace_three_sums (f : V → V → V → ℝ) {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (x : α → V) (y : β → V) (z : γ → V) (x' y' z' : Fin 3 → V)
    (hx : ∀ v w, (∑ a, f (x a) v w) = ∑ a, f (x' a) v w)
    (hy : ∀ u w, (∑ b, f u (y b) w) = ∑ b, f u (y' b) w)
    (hz : ∀ u v, (∑ d, f u v (z d)) = ∑ d, f u v (z' d)) :
    (∑ a, ∑ b, ∑ d, f (x a) (y b) (z d)) = ∑ a, ∑ b, ∑ d, f (x' a) (y' b) (z' d) := by
  calc
    _ = ∑ a, ∑ b, ∑ d, f (x a) (y b) (z' d) := by simp_rw [hz]
    _ = ∑ a, ∑ d, ∑ b, f (x a) (y b) (z' d) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, f (x a) (y' b) (z' d) := by simp_rw [hy]
    _ = ∑ d, ∑ b, ∑ a, f (x a) (y' b) (z' d) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, f (x' a) (y' b) (z' d) := by simp_rw [hx]
    _ = _ := by
      calc
        _ = ∑ d, ∑ a, ∑ b, f (x' a) (y' b) (z' d) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ a, ∑ d, ∑ b, f (x' a) (y' b) (z' d) := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [FiniteDimensional ℝ V] in
private theorem centered_trace_offset
    (orth : U.IsOrtho U') (orthW : U.IsOrtho W) (orth'W : U'.IsOrtho W)
    (g : SymmetricCubic E) (unit : ∀ x, g.L e x = x)
    (F : CenteredTraceFrame J e U)
    (G : CenteredTraceFrame J e U')
    (H : CenteredTraceFrame J e W) (a b d : Fin 3) :
    g.apply (J (F.centered a : V)) (J (G.centered b : V)) (J (H.centered d : V)) =
      g.apply (F.point a) (G.point b) (H.point d) - 1 / 9 := by
  let x := J (F.centered a : V)
  let y := J (G.centered b : V)
  let z := J (H.centered d : V)
  have px : F.point a = x + (1 / 3 : ℝ) • e := by rw [show x = _ from F.centered_eq a, sub_add_cancel]
  have py : G.point b = y + (1 / 3 : ℝ) • e := by rw [show y = _ from G.centered_eq b, sub_add_cancel]
  have pz : H.point d = z + (1 / 3 : ℝ) • e := by rw [show z = _ from H.centered_eq d, sub_add_cancel]
  have hxy : ⟪x, y⟫ = 0 := (J.inner_map_map ..).trans
    (orth.inner_eq (F.centered a).property (G.centered b).property)
  have hxz : ⟪x, z⟫ = 0 := (J.inner_map_map ..).trans
    (orthW.inner_eq (F.centered a).property (H.centered d).property)
  have hyz : ⟪y, z⟫ = 0 := (J.inner_map_map ..).trans
    (orth'W.inner_eq (G.centered b).property (H.centered d).property)
  have hxe : ⟪x, e⟫ = 0 := F.centered_inner_unit a
  have hye : ⟪y, e⟫ = 0 := G.centered_inner_unit b
  have hze : ⟪z, e⟫ = 0 := H.centered_inner_unit d
  have hey : ⟪e, y⟫ = 0 := (real_inner_comm _ _).trans hye
  have hez : ⟪e, z⟫ = 0 := (real_inner_comm _ _).trans hze
  have e₁ (u v : E) : g.apply e u v = ⟪u, v⟫ := by simp [SymmetricCubic.apply, unit]
  have e₂ (u v : E) : g.apply u e v = ⟪u, v⟫ :=
    (g.apply_swap₁₂ _ _ _).trans (e₁ _ _)
  have e₃ (u v : E) : g.apply u v e = ⟪u, v⟫ :=
    (g.apply_swap₂₃ _ _ _).trans (e₂ _ _)
  change g.apply x y z = _
  rw [px, py, pz]
  simp only [SymmetricCubic.apply_add₁, SymmetricCubic.apply_add₂, SymmetricCubic.apply_add₃,
    SymmetricCubic.apply_smul₁, SymmetricCubic.apply_smul₂, SymmetricCubic.apply_smul₃,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    e₁, e₂, e₃, hxy, hxz, hyz, hxe, hey, hez, F.unit_inner_self]
  ring

/-- The point formula for three centered frame planes in a trace-normalized unital
metric algebra. The frame hypotheses supply the centered spanning sets. -/
theorem shareOfThreePlanes_eq_centered_frame_trace (round : IsRound h (1 / 6))
    (orth : U.IsOrtho U') (orthW : U.IsOrtho W) (orth'W : U'.IsOrtho W)
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2)
    (g : SymmetricCubic E) (unit : ∀ x, g.L e x = x)
    (metric : ∀ x y z, h.apply x y z = g.apply (J x) (J y) (J z))
    (F : CenteredTraceFrame J e U) (G : CenteredTraceFrame J e U')
    (H : CenteredTraceFrame J e W) :
    shareOfThreePlanes h U U' W =
      6 * ∑ a, ∑ b, ∑ d, (g.apply (F.point a) (G.point b) (H.point d) - 1 / 9) ^ 2 := by
  let X := stdOrthonormalBasis ℝ U
  let Y := stdOrthonormalBasis ℝ U'
  let Z := stdOrthonormalBasis ℝ W
  rw [shareOfThreePlanes_eq_sum_cubic_sq round orth closed closed' dim X Y Z]
  have hs := replace_three_sums (fun x y z : V => (h.apply x y z) ^ 2)
      (fun a => (X a : V)) (fun b => (Y b : V)) (fun d => (Z d : V))
      (fun a => (F.centered a : V)) (fun b => (G.centered b : V)) (fun d => (H.centered d : V))
      (fun y z => ?_) (fun x z => ?_) (fun x y => ?_)
  · rw [hs]
    simp_rw [metric, centered_trace_offset orth orthW orth'W g unit F G H]
    norm_num
  · simp_rw [h.apply_swap₁₂ _ y, h.apply_swap₂₃ y _ z]
    exact (F.sum_sq_functional ((h.trilinear y z).comp U.subtype) X).symm
  · simp_rw [h.apply_swap₂₃ x _ z]
    exact (G.sum_sq_functional ((h.trilinear x z).comp U'.subtype) Y).symm
  · exact (H.sum_sq_functional ((h.trilinear x y).comp W.subtype) Z).symm

end
end ThirteenPlanes.RoundCubics
