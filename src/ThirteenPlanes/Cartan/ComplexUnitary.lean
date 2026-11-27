module

public import ThirteenPlanes.Cartan.ComplexJordan
public import ThirteenPlanes.Cartan.JordanAction
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Basic

@[expose] public section

set_option backward.privateInPublic true

/-! The native special-unitary action on complex Hermitian matrices. -/

namespace ThirteenPlanes.Cartan

open scoped Matrix RealInnerProductSpace
open RoundCubics Unitary

noncomputable section

abbrev ComplexUnitary3 := Matrix.unitaryGroup (Fin 3) ℂ
abbrev ComplexSpecialUnitary3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

def complexMatrixAd (U : ComplexUnitary3) : ComplexMatrix3 ≃⋆ₐ[ℂ] ComplexMatrix3 :=
  Unitary.conjStarAlgAut ℂ _ U

@[simp] theorem complexMatrixAd_apply (U : ComplexUnitary3) (X : ComplexMatrix3) :
    complexMatrixAd U X = (U : ComplexMatrix3) * X * (U : ComplexMatrix3)ᴴ := by
  simp [complexMatrixAd, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

private theorem complexMatrixAd_star_apply (U : ComplexUnitary3) (X : ComplexMatrix3) :
    complexMatrixAd (star U) X = (U : ComplexMatrix3)ᴴ * X * (U : ComplexMatrix3) := by
  simp [complexMatrixAd_apply, Matrix.star_eq_conjTranspose]

theorem complexMatrixAd_preserves_trace (U : ComplexUnitary3) (X : ComplexMatrix3) :
    Matrix.trace (complexMatrixAd U X) = Matrix.trace X := by
  rw [complexMatrixAd_apply, Matrix.trace_mul_comm ((U : ComplexMatrix3) * X), ← mul_assoc]
  have h : (U : ComplexMatrix3)ᴴ * (U : ComplexMatrix3) = 1 := Unitary.coe_star_mul_self U
  rw [h, one_mul]

theorem complexMatrixAd_inv (U : ComplexUnitary3) (X : ComplexMatrix3) :
    complexMatrixAd (star U) (complexMatrixAd U X) = X := by
  rw [complexMatrixAd_star_apply, complexMatrixAd_apply]
  have h₁ : (U : ComplexMatrix3)ᴴ * (U : ComplexMatrix3) = 1 := Unitary.coe_star_mul_self U
  calc
    _ = ((U : ComplexMatrix3)ᴴ * (U : ComplexMatrix3)) * X * ((U : ComplexMatrix3)ᴴ * (U : ComplexMatrix3)) := by
      simp only [mul_assoc]
    _ = X := by rw [h₁, one_mul, mul_one]

private def complexUnitaryOnFull (U : ComplexUnitary3) (x : FullHermitian) : FullHermitian :=
  ofFullMatrix (complexMatrixAd U (fullMatrix x)) (by
    change star (complexMatrixAd U (fullMatrix x)) = _
    rw [← map_star]
    exact congrArg (complexMatrixAd U) (fullMatrix_hermitian x).eq)

@[simp] private theorem fullMatrix_unitaryOnFull (U : ComplexUnitary3) (x : FullHermitian) :
    fullMatrix (complexUnitaryOnFull U x) = complexMatrixAd U (fullMatrix x) :=
  fullMatrix_ofFullMatrix _ _

/-- Unitary matrix conjugation preserves both the complex Hermitian Jordan product and trace metric. -/
def complexUnitaryAction (U : ComplexUnitary3) : complexJordan.Automorphism where
  action :=
    { toFun := complexUnitaryOnFull U
      invFun := complexUnitaryOnFull (star U)
      left_inv := fun x => fullMatrix_injective (by
        simp only [fullMatrix_unitaryOnFull, complexMatrixAd_inv])
      right_inv := fun x => fullMatrix_injective (by
        have h := complexMatrixAd_inv (star U) (fullMatrix x)
        rw [star_star] at h
        simpa only [fullMatrix_unitaryOnFull] using h)
      map_add' := fun x y => fullMatrix_injective (by
        simp only [fullMatrix_unitaryOnFull, map_add])
      map_smul' := fun r x => fullMatrix_injective (by
        simp only [fullMatrix_unitaryOnFull, map_smul, RingHom.id_apply, complexMatrixAd_apply,
          Matrix.smul_mul, Matrix.mul_smul])
      norm_map' := fun x => by
        change ‖complexUnitaryOnFull U x‖ = ‖x‖
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, fullInner_eq_tracePairing,
          fullInner_eq_tracePairing, fullMatrix_unitaryOnFull]
        unfold tracePairing
        rw [← map_mul, complexMatrixAd_preserves_trace] }
  unit_fixed := by
    apply fullMatrix_injective
    change fullMatrix (complexUnitaryOnFull U complexUnit) = fullMatrix complexUnit
    rw [fullMatrix_unitaryOnFull, fullMatrix_complexUnit, map_one]
  product_map := fun x y => by
    apply fullMatrix_injective
    change fullMatrix (complexUnitaryOnFull U (complexFullCubic.L x y)) =
      fullMatrix (complexFullCubic.L (complexUnitaryOnFull U x) (complexUnitaryOnFull U y))
    simp only [fullMatrix_unitaryOnFull, fullMatrix_complexFullCubic_product, symmetricMatrixProduct,
      map_add, map_mul, map_smul]

/-- The actual special unitary group acting on the rank-three trace-metric Jordan algebra. -/
def complexSU3Action (U : ComplexSpecialUnitary3) : complexJordan.Automorphism :=
  complexUnitaryAction (⟨U.val, U.property.1⟩ : ComplexUnitary3)

@[simp] theorem complexUnitaryAction_matrix (U : ComplexUnitary3) (x : FullHermitian) :
    fullMatrix ((complexUnitaryAction U).action x) = complexMatrixAd U (fullMatrix x) :=
  fullMatrix_unitaryOnFull U x

@[simp] theorem complexUnitaryAction_trace_matrix (U : ComplexUnitary3) (x : complexJordan.traceFree) :
    fullMatrix (((complexUnitaryAction U).traceAction complexJordan) x).val =
      complexMatrixAd U (fullMatrix x.val) := fullMatrix_unitaryOnFull U x.val

theorem complexUnitary_cubeRoot_det_correction (U : ComplexUnitary3) :
    ∃ z : ℂ, z ^ 3 = (U.val.det)⁻¹ ∧ z * star z = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (U.val.det)⁻¹ (n := 3) (by decide)
  have hn : ‖U.val.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.property)
  have hzn : ‖z‖ = 1 := (pow_left_inj₀ (norm_nonneg z) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp (by
    rw [← norm_pow, hz, norm_inv, hn, inv_one, one_pow])
  exact ⟨z, hz, by
    change z * (starRingEnd ℂ) z = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]
    norm_num⟩

/-- Every unitary conjugation is a special-unitary conjugation, by scalar rephasing. -/
theorem complexUnitary_exists_SU3_sameMatrixAd (U : ComplexUnitary3) :
    ∃ W : ComplexSpecialUnitary3, ∀ X : ComplexMatrix3,
      complexMatrixAd (⟨W.val, W.property.1⟩ : ComplexUnitary3) X = complexMatrixAd U X := by
  obtain ⟨z, hz, hu⟩ := complexUnitary_cubeRoot_det_correction U
  let A : ComplexMatrix3 := z • U.val
  have hdet : A.det = 1 := by
    rw [show A = z • U.val from rfl, Matrix.det_smul, Fintype.card_fin, hz,
      inv_mul_cancel₀ (show U.val.det ≠ 0 from fun h => by
        have hm := (Matrix.det_of_mem_unitary U.property).2
        rw [h, zero_mul] at hm
        exact zero_ne_one hm)]
  have hr : A * Aᴴ = 1 := by
    have hU : (U.val : ComplexMatrix3) * (U.val : ComplexMatrix3)ᴴ = 1 := Unitary.coe_mul_star_self U
    rw [show A = z • U.val from rfl, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hu, one_smul, hU]
  let W : ComplexSpecialUnitary3 := ⟨A, Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr hr, hdet⟩⟩
  refine ⟨W, fun X => ?_⟩
  rw [complexMatrixAd_apply, complexMatrixAd_apply]
  change (z • U.val) * X * (z • U.val)ᴴ = U.val * X * U.valᴴ
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hu, one_smul]

/-- The unitary action on Hermitian matrices is realized by an actual special unitary. -/
theorem complexUnitary_exists_SU3_sameAction (U : ComplexUnitary3) :
    ∃ W : ComplexSpecialUnitary3, ∀ x,
      (complexSU3Action W).action x = (complexUnitaryAction U).action x := by
  obtain ⟨W, hW⟩ := complexUnitary_exists_SU3_sameMatrixAd U
  refine ⟨W, fun x => fullMatrix_injective ?_⟩
  rw [complexSU3Action, complexUnitaryAction_matrix, complexUnitaryAction_matrix]
  exact hW (fullMatrix x)

end

end ThirteenPlanes.Cartan
