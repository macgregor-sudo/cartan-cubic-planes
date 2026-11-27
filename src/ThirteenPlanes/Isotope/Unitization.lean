module

public import CompositionAlgebras.Composition.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

namespace ThirteenPlanes.MarkedPlane

open scoped RealInnerProductSpace

variable {S₁ S₂ S₃ : Type*}
  [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁]
  [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂]
  [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃]

/-- Identifying the two input slots with the output slot gives a unital product
on the output and retains the original bilinear map. -/
structure OrthogonalProductUnitization (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) where
  left : S₁ ≃ₗᵢ[ℝ] S₃
  right : S₂ ≃ₗᵢ[ℝ] S₃
  unit : S₃
  product : S₃ →ₗ[ℝ] S₃ →ₗ[ℝ] S₃
  one_mul : ∀ q, product unit q = q
  mul_one : ∀ p, product p unit = p
  norm_mul : ∀ p q, ‖product p q‖ = ‖p‖ * ‖q‖
  product_apply : ∀ u y, product (left u) (right y) = φ u y

section

variable [FiniteDimensional ℝ S₁] [FiniteDimensional ℝ S₂] [FiniteDimensional ℝ S₃]

/-- Fixing one unit vector in each input slot makes the two partial products
onto isometries. Transport along their inverses supplies the product and unit. -/
noncomputable def unitizeOrthogonalProductAt
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃)
    (hφ : ∀ u y, ‖φ u y‖ = ‖u‖ * ‖y‖)
    (h₁ : Module.finrank ℝ S₁ = Module.finrank ℝ S₃)
    (h₂ : Module.finrank ℝ S₂ = Module.finrank ℝ S₃)
    (u₀ : S₁) (y₀ : S₂) (hu₀ : ‖u₀‖ = 1) (hy₀ : ‖y₀‖ = 1) :
    OrthogonalProductUnitization φ := by
  let left : S₁ →ₗᵢ[ℝ] S₃ :=
    ⟨φ.flip y₀, fun u => by simpa only [LinearMap.flip_apply, hy₀, mul_one] using hφ u y₀⟩
  let right : S₂ →ₗᵢ[ℝ] S₃ :=
    ⟨φ u₀, fun y => by simpa only [hu₀, one_mul] using hφ u₀ y⟩
  let L := left.toLinearIsometryEquiv h₁
  let R := right.toLinearIsometryEquiv h₂
  have hL (u : S₁) : L u = φ u y₀ := rfl
  have hR (y : S₂) : R y = φ u₀ y := rfl
  refine ⟨L, R, φ u₀ y₀, φ.compl₁₂ L.symm.toLinearEquiv.toLinearMap
    R.symm.toLinearEquiv.toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro q
    change φ (L.symm (φ u₀ y₀)) (R.symm q) = q
    rw [← hL u₀, L.symm_apply_apply, ← hR, R.apply_symm_apply]
  · intro p
    change φ (L.symm p) (R.symm (φ u₀ y₀)) = p
    rw [← hR y₀, R.symm_apply_apply, ← hL, L.apply_symm_apply]
  · intro p q
    change ‖φ (L.symm p) (R.symm q)‖ = ‖p‖ * ‖q‖
    rw [hφ, L.symm.norm_map, R.symm.norm_map]
  · intro u y
    change φ (L.symm (L u)) (R.symm (R y)) = φ u y
    rw [L.symm_apply_apply, R.symm_apply_apply]

/-- A norm-multiplicative bilinear map on three Euclidean spaces of equal
positive dimension gives a unital norm-multiplicative product on its output. -/
theorem orthogonalProduct_hasUnitization
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃)
    (hφ : ∀ u y, ‖φ u y‖ = ‖u‖ * ‖y‖)
    (h₁ : Module.finrank ℝ S₁ = Module.finrank ℝ S₃)
    (h₂ : Module.finrank ℝ S₂ = Module.finrank ℝ S₃)
    (h₃ : 0 < Module.finrank ℝ S₃) :
    Nonempty (OrthogonalProductUnitization φ) := by
  let : Nontrivial S₁ := Module.nontrivial_of_finrank_pos (h₁.symm ▸ h₃)
  let : Nontrivial S₂ := Module.nontrivial_of_finrank_pos (h₂.symm ▸ h₃)
  obtain ⟨u₀, hu₀⟩ := exists_norm_eq S₁ zero_le_one
  obtain ⟨y₀, hy₀⟩ := exists_norm_eq S₂ zero_le_one
  exact ⟨unitizeOrthogonalProductAt φ hφ h₁ h₂ u₀ y₀ hu₀ hy₀⟩

end

namespace OrthogonalProductUnitization

variable {φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃} (U : OrthogonalProductUnitization φ)

/-- The unital ring structure carried by the transported product. -/
@[instance_reducible]
def toNonAssocRing : NonAssocRing S₃ where
  __ := (inferInstance : AddCommGroup S₃)
  one := U.unit
  mul x y := U.product x y
  one_mul := U.one_mul
  mul_one := U.mul_one
  left_distrib x y z := (U.product x).map_add y z
  right_distrib x y z := LinearMap.congr_fun (U.product.map_add x y) z
  zero_mul x := LinearMap.congr_fun U.product.map_zero x
  mul_zero x := (U.product x).map_zero

theorem toIsScalarTower : letI := U.toNonAssocRing; IsScalarTower ℝ S₃ S₃ := by
  let := U.toNonAssocRing
  exact ⟨fun r x y => LinearMap.congr_fun (U.product.map_smul r x) y⟩

theorem toSMulCommClass : letI := U.toNonAssocRing; SMulCommClass ℝ S₃ S₃ := by
  let := U.toNonAssocRing
  exact ⟨fun r x y => ((U.product x).map_smul r y).symm⟩

/-- The transported product composes the original Euclidean inner product. -/
@[instance_reducible]
noncomputable def toCompositionAlgebra :
    letI := U.toNonAssocRing
    letI := U.toIsScalarTower
    letI := U.toSMulCommClass
    CompositionAlgebra S₃ := by
  letI := U.toNonAssocRing
  letI := U.toIsScalarTower
  letI := U.toSMulCommClass
  refine ⟨innerₗ S₃, fun x y => real_inner_comm y x, ?_, ?_⟩
  · intro x hx
    change 0 < ⟪x, x⟫
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)
  · intro p q
    change ⟪U.product p q, U.product p q⟫ = ⟪p, p⟫ * ⟪q, q⟫
    simp only [real_inner_self_eq_norm_sq, U.norm_mul, mul_pow]

theorem compositionNorm_eq (p : S₃) :
    letI := U.toNonAssocRing
    letI := U.toIsScalarTower
    letI := U.toSMulCommClass
    letI := U.toCompositionAlgebra
    CompositionAlgebra.nf p = ‖p‖ ^ 2 :=
  real_inner_self_eq_norm_sq p

end OrthogonalProductUnitization
end ThirteenPlanes.MarkedPlane
