module

public import ThirteenPlanes.Cartan.DerivationGradingCore
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

set_option backward.privateInPublic true

/-! Decomposition of every complex derivation into its homogeneous pieces. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

variable {A : Type*} [AddCommGroup A] [Module ℂ A]
variable (M : NormalizedTernaryBasis A)

/-- All complex-linear derivations of the specified product. -/
def derivations : Submodule ℂ (Module.End ℂ A) where
  carrier := {D | M.IsDerivation D}
  zero_mem' := by intro x y; simp
  add_mem' := by
    rintro D E hD hE x y
    simp only [LinearMap.add_apply, hD x y, hE x y, map_add]
    abel
  smul_mem' := by
    rintro a D hD x y
    simp only [LinearMap.smul_apply, hD x y, map_smul, smul_add]

@[simp] theorem mem_derivations {D : Module.End ℂ A} :
    D ∈ M.derivations ↔ M.IsDerivation D := Iff.rfl

/-- The projection to a single character line, in the normalized character basis. -/
def vectorProjection (g : Charge) : A →ₗ[ℂ] A :=
  (M.basis.coord g).smulRight (M.basis g)

theorem vectorProjection_apply (g : Charge) (x : A) :
    M.vectorProjection g x = M.basis.coord g x • M.basis g := rfl

@[simp] theorem vectorProjection_basis (g h : Charge) :
    M.vectorProjection g (M.basis h) = if g = h then M.basis h else 0 := by
  classical
  rw [vectorProjection_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases hgh : g = h
  · simp [hgh]
  · simp [hgh, Ne.symm hgh]

/-- The projection of a complex endomorphism to the given degree. -/
def degreeProjection (γ : Charge) (D : Module.End ℂ A) : Module.End ℂ A :=
  M.basis.constr ℂ fun g => M.vectorProjection (g + γ) (D (M.basis g))

@[simp] theorem degreeProjection_basis (γ g : Charge) (D : Module.End ℂ A) :
    M.degreeProjection γ D (M.basis g) = M.vectorProjection (g + γ) (D (M.basis g)) :=
  M.basis.constr_basis ℂ _ g

/-- The degree projection is linear as a function of endomorphisms. -/
def degreeProjectionLinear (γ : Charge) : Module.End ℂ A →ₗ[ℂ] Module.End ℂ A where
  toFun := M.degreeProjection γ
  map_add' D E := by apply M.basis.ext; intro g; simp
  map_smul' a D := by apply M.basis.ext; intro g; simp

theorem degreeProjection_hasDegree (γ : Charge) (D : Module.End ℂ A) :
    M.HasDegree (M.degreeProjection γ D) γ := by
  intro g
  exact ⟨M.basis.coord (g + γ) (D (M.basis g)), by
    rw [degreeProjection_basis, vectorProjection_apply]⟩

private theorem vectorProjection_product_left (g h γ : Charge) (x : A) :
    M.vectorProjection (g + h + γ) (M.product x (M.basis h)) =
      M.product (M.vectorProjection (g + γ) x) (M.basis h) := by
  let L := M.product.flip (M.basis h)
  suffices (M.vectorProjection (g + h + γ)).comp L =
      L.comp (M.vectorProjection (g + γ)) from LinearMap.congr_fun this x
  apply M.basis.ext
  intro k
  change M.vectorProjection (g + h + γ) (M.product (M.basis k) (M.basis h)) =
    M.product (M.vectorProjection (g + γ) (M.basis k)) (M.basis h)
  obtain ⟨c, hc⟩ := M.homogeneous_product k h
  rw [hc, map_smul, vectorProjection_basis, vectorProjection_basis]
  by_cases hk : g + γ = k
  · rw [ite_eq_left hk, hc, show g + h + γ = k + h by rw [← hk]; abel]
    simp
  · have hne : g + h + γ ≠ k + h := by
      intro he
      apply hk
      apply add_right_cancel (b := h)
      rw [← he]
      abel
    rw [ite_eq_right hk, ite_eq_right hne, smul_zero, map_zero, LinearMap.zero_apply]

private theorem vectorProjection_product_right (g h γ : Charge) (y : A) :
    M.vectorProjection (g + h + γ) (M.product (M.basis g) y) =
      M.product (M.basis g) (M.vectorProjection (h + γ) y) := by
  rw [M.comm (M.basis g) y, M.comm (M.basis g) (M.vectorProjection (h + γ) y), add_comm g h]
  exact M.vectorProjection_product_left h g γ y

/-- Preservation of the derivation rule on one pair needs only its original equality on that pair. -/
theorem degreeProjection_derivation_on_basis {D : Module.End ℂ A}
    (γ g h : Charge)
    (hd : D (M.product (M.basis g) (M.basis h)) =
      M.product (D (M.basis g)) (M.basis h) + M.product (M.basis g) (D (M.basis h))) :
    M.degreeProjection γ D (M.product (M.basis g) (M.basis h)) =
      M.product (M.degreeProjection γ D (M.basis g)) (M.basis h) +
      M.product (M.basis g) (M.degreeProjection γ D (M.basis h)) := by
  have hEq := congrArg (M.vectorProjection (g + h + γ)) hd
  rw [map_add, M.vectorProjection_product_left, M.vectorProjection_product_right,
    ← M.degreeProjection_basis, ← M.degreeProjection_basis] at hEq
  obtain ⟨c, hc⟩ := M.homogeneous_product g h
  rw [hc, map_smul, map_smul] at hEq
  rw [hc, map_smul, M.degreeProjection_basis]
  exact hEq

/-- Taking one homogeneous component of an actual derivation preserves the derivation rule. -/
theorem degreeProjection_mem_derivationGrade {D : Module.End ℂ A}
    (hd : M.IsDerivation D) (γ : Charge) :
    M.degreeProjection γ D ∈ M.derivationGrade γ := by
  refine M.mem_derivationGrade.mpr ⟨?_, M.degreeProjection_hasDegree γ D⟩
  let T := M.degreeProjection γ D
  have he (g : Charge) : T.comp (M.product (M.basis g)) =
      M.product (T (M.basis g)) + (M.product (M.basis g)).comp T := by
    apply M.basis.ext
    intro h
    exact M.degreeProjection_derivation_on_basis γ g h (hd (M.basis g) (M.basis h))
  intro x y
  have hh : T.comp (M.product.flip y) =
      (M.product.flip y).comp T + M.product.flip (T y) := by
    apply M.basis.ext
    intro g
    exact LinearMap.congr_fun (he g) y
  exact LinearMap.congr_fun hh x

/-- Summing the projections over all 27 shifts recovers the linear operator. -/
theorem sum_degreeProjection (D : Module.End ℂ A) : ∑ γ, M.degreeProjection γ D = D := by
  classical
  apply M.basis.ext
  intro g
  simp only [LinearMap.sum_apply, degreeProjection_basis]
  calc
    _ = ∑ h, M.vectorProjection h (D (M.basis g)) :=
      Equiv.sum_comp (Equiv.addLeft g) _
    _ = D (M.basis g) := by simp [vectorProjection_apply, Basis.coord_apply]

theorem degreeProjection_of_mem_derivationGrade {D : Module.End ℂ A} {γ : Charge}
    (hD : D ∈ M.derivationGrade γ) (δ : Charge) :
    M.degreeProjection δ D = if δ = γ then D else 0 := by
  classical
  apply M.basis.ext
  intro g
  rw [degreeProjection_basis, M.derivationGrade_apply hD g, map_smul, vectorProjection_basis]
  by_cases he : δ = γ
  · subst δ
    simp [M.derivationGrade_apply hD g]
  · have hne : g + δ ≠ g + γ := fun h => he (add_left_cancel h)
    simp [he, hne]

theorem derivationGrades_iSup_eq : (⨆ γ, M.derivationGrade γ) = M.derivations := by
  apply le_antisymm
  · refine iSup_le fun γ D hD => ?_
    exact (M.mem_derivationGrade.mp hD).1
  · intro D hD
    rw [← M.sum_degreeProjection D]
    exact Submodule.sum_mem _ fun γ _ => (le_iSup (fun γ => M.derivationGrade γ) γ)
      (M.degreeProjection_mem_derivationGrade hD γ)

theorem derivationGrades_independent :
    iSupIndep (fun γ => M.derivationGrade γ) := by
  classical
  rw [iSupIndep_def]
  intro γ
  rw [Submodule.disjoint_def]
  intro D hD hrest
  have hself : M.degreeProjection γ D = D := by
    rw [M.degreeProjection_of_mem_derivationGrade hD, ite_eq_left rfl]
  have hker : (⨆ (δ : Charge) (_ : δ ≠ γ), M.derivationGrade δ) ≤
      (M.degreeProjectionLinear γ).ker := by
    refine iSup_le fun δ => iSup_le fun hd E hE => ?_
    change M.degreeProjection γ E = 0
    rw [M.degreeProjection_of_mem_derivationGrade hE, ite_eq_right (Ne.symm hd)]
  have hz : M.degreeProjection γ D = 0 := hker hrest
  exact hself.symm.trans hz

end
end ThirteenPlanes.Cartan.NormalizedTernaryBasis
