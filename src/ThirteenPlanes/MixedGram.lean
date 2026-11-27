module

public import ThirteenPlanes.ClosedPieces
public import ThirteenPlanes.MixedProducts
public import ThirteenPlanes.RoundContractions
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators InnerProductSpace RealInnerProductSpace TensorProduct

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {h : SymmetricCubic V} {c : ℝ} {U U' : Submodule ℝ V}

/-- Multiplication by a vector in a closed subspace preserves its orthogonal complement. -/
theorem closedPiece_mul_mem_orthogonal (closed : IsClosedPiece h U)
    (x : U) (z : Uᗮ) : h.L (x : V) (z : V) ∈ Uᗮ := by
  apply (U.mem_orthogonal _).mpr
  intro w hw
  rw [← h.L_isSymmetric (x : V) w z]
  exact Submodule.inner_right_of_mem_orthogonal (closed x.property hw) z.property

/-- The multiplication slices of a closed subspace acting on its complement. -/
def orthogonalSlice (closed : IsClosedPiece h U) : U →ₗ[ℝ] Module.End ℝ Uᗮ :=
  LinearMap.mk₂ ℝ
    (fun x z => ⟨h.L (x : V) (z : V), closedPiece_mul_mem_orthogonal closed x z⟩)
    (by intro x y z; apply Subtype.ext; exact LinearMap.congr_fun (h.L.map_add (x : V) y) z)
    (by intro r x z; apply Subtype.ext; exact LinearMap.congr_fun (h.L.map_smul r (x : V)) z)
    (by intro x y z; apply Subtype.ext; exact (h.L (x : V)).map_add (y : V) z)
    (by intro r x z; apply Subtype.ext; exact (h.L (x : V)).map_smul r (z : V))

@[simp] theorem orthogonalSlice_apply (closed : IsClosedPiece h U) (x : U) (z : Uᗮ) :
    (orthogonalSlice closed x z : V) = h.L (x : V) (z : V) := rfl

private theorem square_operator_at_strength (round : IsRound h c) (x y : V) :
    h.L (h.L x x) y + (2 : ℝ) • h.L x (h.L x y) =
      (c * ‖x‖ ^ 2) • y + (2 * c * ⟪x, y⟫) • x := by
  apply ext_inner_right ℝ
  intro z
  have hp := polarized round x x y z
  have h₁ : ⟪h.L (h.L x x) y, z⟫ = ⟪h.L x x, h.L y z⟫ := by
    rw [h.L_comm (h.L x x) y]
    exact h.L_isSymmetric y _ _
  have h₂ := h.L_isSymmetric x (h.L x y) z
  have h₃ : ⟪h.L x (h.L x y), z⟫ = ⟪h.L x z, h.L x y⟫ :=
    h₂.trans (real_inner_comm _ _)
  simp only [real_inner_self_eq_norm_sq, ← h₁, ← h₂, ← h₃] at hp
  simp only [inner_add_left, real_inner_smul_left]
  linear_combination hp

variable [FiniteDimensional ℝ V]

private theorem orthogonalSlice_commutes_square (round : IsRound h c)
    (closed : IsClosedPiece h U) (x : U) :
    Commute (orthogonalSlice closed x) (orthogonalSlice closed ((h.pullback U.subtype).L x x)) := by
  let L := orthogonalSlice closed
  have hsq : L ((h.pullback U.subtype).L x x) + (2 : ℝ) • (L x) ^ 2 =
      (c * ‖x‖ ^ 2) • (1 : Module.End ℝ Uᗮ) := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change h.L ((h.pullback U.subtype).L x x : V) (z : V) +
      (2 : ℝ) • h.L (x : V) (h.L (x : V) (z : V)) = (c * ‖(x : V)‖ ^ 2) • (z : V)
    rw [closedSubspace_restriction_product closed]
    have horth := Submodule.inner_right_of_mem_orthogonal x.property z.property
    simpa only [horth, mul_zero, zero_smul, add_zero] using
      square_operator_at_strength round (x : V) (z : V)
  change Commute (L x) (L ((h.pullback U.subtype).L x x))
  rw [eq_sub_iff_add_eq.mpr hsq]
  exact ((Commute.one_right (L x)).smul_right _).sub_right
    (((Commute.refl (L x)).pow_right 2).smul_right (2 : ℝ))

/-- All multiplication slices of a closed round plane commute on its complement. -/
theorem closedPlane_slices_commute (round : IsRound h c) (closed : IsClosedPiece h U)
    (dim : Module.finrank ℝ U = 2) (x y : U) :
    Commute (orthogonalSlice closed x) (orthogonalSlice closed y) := by
  let e := (stdOrthonormalBasis ℝ U).reindex (finCongr dim)
  let a := e 0
  let b := e 1
  let g := h.pullback U.subtype
  let L := orthogonalSlice closed
  have gr : IsRound g c := closedSubspace_restriction_isRound round closed
  have gt : g.TraceFree := traceFree_of_round_finrank_two gr dim
  have expand (z : U) : z = ⟪a, z⟫ • a + ⟪b, z⟫ • b := by
    simpa only [Fin.sum_univ_two] using (e.sum_repr' z).symm
  have hsum : g.L a a + g.L b b = 0 := by
    apply ext_inner_right ℝ
    intro z
    have hd (w : U) : ⟪w, g.L z w⟫ = ⟪g.L w w, z⟫ :=
      (real_inner_comm _ _).trans ((g.apply_swap₁₂ z w w).trans (g.apply_swap₂₃ w z w))
    have ht := gt z
    rw [SymmetricCubic.trace_eq_sum_inner e, Fin.sum_univ_two, hd, hd] at ht
    simpa only [inner_add_left, inner_zero_left] using ht
  have hb : g.L b b = -(g.L a a) :=
    eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hsum)
  let α := ⟪a, g.L a a⟫
  let β := ⟪b, g.L a a⟫
  have ha : g.L a a = α • a + β • b := expand (g.L a a)
  have hab : Commute (L a) (L b) := by
    by_cases hβ : β = 0
    · have hα : α ≠ 0 := by
        intro hz
        have hv : g.L a a = 0 := by
          rw [ha, hz, hβ, zero_smul, zero_smul, add_zero]
        have hr := gr.square_norm a
        change ‖g.L a a‖ ^ 2 = c * ‖a‖ ^ 4 at hr
        rw [hv, norm_zero, show ‖a‖ = 1 from e.orthonormal.norm_eq_one 0] at hr
        exact gr.positive.ne' (by simpa using hr.symm)
      have hb' : g.L b b = (-α) • a := by
        rw [hb, ha, hβ, zero_smul, add_zero, neg_smul]
      have hc : Commute (L b) (L (g.L b b)) := orthogonalSlice_commutes_square round closed b
      rw [hb', map_smul] at hc
      exact ((Commute.smul_right_iff₀ (neg_ne_zero.mpr hα)).mp hc).symm
    · have hc : Commute (L a) (L (g.L a a)) := orthogonalSlice_commutes_square round closed a
      rw [ha, map_add, map_smul, map_smul] at hc
      have hs : Commute (L a) (α • L a) := (Commute.refl (L a)).smul_right α
      have ht : Commute (L a) (β • L b) := by
        simpa only [add_sub_cancel_left] using hc.sub_right hs
      exact (Commute.smul_right_iff₀ hβ).mp ht
  have hz (z : U) : Commute (L a) (L z) ∧ Commute (L b) (L z) := by
    rw [expand z, map_add, map_smul, map_smul]
    exact ⟨((Commute.refl (L a)).smul_right _).add_right (hab.smul_right _),
      (hab.symm.smul_right _).add_right ((Commute.refl (L b)).smul_right _)⟩
  change Commute (L x) (L y)
  rw [expand x, map_add, map_smul, map_smul]
  exact (((hz y).1).smul_left _).add_left (((hz y).2).smul_left _)

/-- The mixed products of a closed round plane with an orthogonal closed subspace
have the tensor-product Gram form. -/
theorem mixedProduct_gram (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (x x' : U) (y y' : U') :
    ⟪h.L (x : V) (y : V), h.L (x' : V) (y' : V)⟫ =
      (c / 2) * (⟪x, x'⟫ * ⟪y, y'⟫) := by
  let z : Uᗮ := ⟨(y : V), Submodule.isOrtho_iff_le.mp orth.symm y.property⟩
  have hc := congrArg (fun A : Module.End ℝ Uᗮ => (A z : V))
    (closedPlane_slices_commute round closed dim x x').eq
  change h.L (x : V) (h.L (x' : V) (y : V)) =
    h.L (x' : V) (h.L (x : V) (y : V)) at hc
  have hab : ⟪h.L (x : V) (y' : V), h.L (x' : V) (y : V)⟫ =
      ⟪h.L (x : V) (y : V), h.L (x' : V) (y' : V)⟫ := by
    rw [real_inner_comm (h.L (x' : V) (y : V)) (h.L (x : V) (y' : V)),
      ← h.L_isSymmetric (x : V) _ _, hc, h.L_isSymmetric (x' : V) _ _]
  have hp := polarized round (x : V) (x' : V) (y : V) (y' : V)
  rw [orth.inner_eq (closed x.property x'.property) (closed' y.property y'.property),
    orth.inner_eq x.property y.property, orth.inner_eq x.property y'.property,
    orth.inner_eq x'.property y.property, orth.inner_eq x'.property y'.property, hab] at hp
  simp only [zero_add, zero_mul, add_zero] at hp
  change _ = (c / 2) * (⟪(x : V), (x' : V)⟫ * ⟪(y : V), (y' : V)⟫)
  linear_combination hp / 2

/-- The mixed multiplication as a linear map on the real metric tensor product. -/
def mixedTensorMap (h : SymmetricCubic V) (U U' : Submodule ℝ V) :
    U ⊗[ℝ] U' →ₗ[ℝ] V :=
  TensorProduct.lift (h.L.compl₁₂ U.subtype U'.subtype)

omit [FiniteDimensional ℝ V] in
@[simp] theorem mixedTensorMap_tmul (h : SymmetricCubic V) (U U' : Submodule ℝ V)
    (x : U) (y : U') : mixedTensorMap h U U' (x ⊗ₜ[ℝ] y) = h.L (x : V) (y : V) := by
  rw [mixedTensorMap, TensorProduct.lift.tmul]
  rfl

/-- The span of mixed products, represented by the range of their linearization. -/
def mixedProductSpace (h : SymmetricCubic V) (U U' : Submodule ℝ V) : Submodule ℝ V :=
  LinearMap.range (mixedTensorMap h U U')

omit [FiniteDimensional ℝ V] in
/-- The tensor range is the submodule spanned by the actual mixed products. -/
theorem mixedProductSpace_eq_span (h : SymmetricCubic V) (U U' : Submodule ℝ V) :
    mixedProductSpace h U U' = Submodule.map₂ h.L U U' := by
  rw [mixedProductSpace, TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  congr 1
  apply TensorProduct.ext'
  intro x y
  simp

/-- The Gram endomorphism of mixed multiplication is scalar on the entire tensor product. -/
theorem mixedTensorMap_adjoint_comp (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) :
    (LinearMap.adjoint (𝕜 := ℝ) (E := U ⊗[ℝ] U') (F := V)
      (mixedTensorMap h U U')).comp (mixedTensorMap h U U') =
      (c / 2) • (LinearMap.id : U ⊗[ℝ] U' →ₗ[ℝ] U ⊗[ℝ] U') := by
  apply TensorProduct.ext'
  intro x y
  apply TensorProduct.ext_iff_inner_right.mpr
  intro x' y'
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, mixedTensorMap_tmul,
    mixedTensorMap_tmul, LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left,
    TensorProduct.inner_tmul]
  exact mixedProduct_gram round orth closed closed' dim x x' y y'

theorem mixedTensorMap_injective (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) : Function.Injective (mixedTensorMap h U U') := by
  apply (LinearMap.adjoint_comp_self_injective_iff
    (𝕜 := ℝ) (E := U ⊗[ℝ] U') (F := V) (mixedTensorMap h U U')).mp
  rw [← LinearMap.coe_comp, mixedTensorMap_adjoint_comp round orth closed closed' dim]
  exact smul_right_injective (U ⊗[ℝ] U') (div_ne_zero round.positive.ne' two_ne_zero)

theorem mixedProductSpace_finrank (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (dim' : Module.finrank ℝ U' = 2) :
    Module.finrank ℝ (mixedProductSpace h U U') = 4 := by
  rw [mixedProductSpace, LinearMap.finrank_range_of_inj
    (mixedTensorMap_injective round orth closed closed' dim), Module.finrank_tensorProduct,
    dim, dim']

theorem mixedProductSpace_le_orthogonal (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U') :
    mixedProductSpace h U U' ≤ (U ⊔ U')ᗮ := by
  rintro v ⟨t, rfl⟩
  refine t.inductionOn ?_ ?_
  · intro x y
    rw [mixedTensorMap_tmul]
    exact ((mixedProductLaw round orth closed closed').1 x.property y.property).1
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The mixed Gram identity, at arbitrary positive round strength. -/
theorem mixedGram (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (dim' : Module.finrank ℝ U' = 2) :
    (∀ (x x' : U) (y y' : U'),
      ⟪h.L (x : V) (y : V), h.L (x' : V) (y' : V)⟫ =
        (c / 2) * (⟪x, x'⟫ * ⟪y, y'⟫)) ∧
    (LinearMap.adjoint (𝕜 := ℝ) (E := U ⊗[ℝ] U') (F := V)
      (mixedTensorMap h U U')).comp (mixedTensorMap h U U') =
      (c / 2) • (LinearMap.id : U ⊗[ℝ] U' →ₗ[ℝ] U ⊗[ℝ] U') ∧
    Module.finrank ℝ (mixedProductSpace h U U') = 4 ∧
    mixedProductSpace h U U' ≤ (U ⊔ U')ᗮ :=
  ⟨mixedProduct_gram round orth closed closed' dim,
    mixedTensorMap_adjoint_comp round orth closed closed' dim,
    mixedProductSpace_finrank round orth closed closed' dim dim',
    mixedProductSpace_le_orthogonal round orth closed closed'⟩

end
end ThirteenPlanes.RoundCubics
