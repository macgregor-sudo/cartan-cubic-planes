module

public import ThirteenPlanes.AlbertGrading.Tits.Product

@[expose] public section

/-!
# first-Tits grading and Weyl basis (i): the maps `Ad_U`, `φ`, `ψ_R`

Each map is complex linear on `FirstTits ℂ`, preserves the unit, the trace form and the square
(hence the product), commutes with `σ`, and restricts to a product-preserving real-linear
bijection of `J_T`. The adjugate covariance `adj(R*a) = adj(a) R` for `R ∈ SU(3)` is the step
named in the paper; for `Ad_U` with `U` merely unitary the two determinant phases cancel.
-/

open scoped Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-! ## Restriction of a `σ`-equivariant complex-linear bijection to `J_T` -/

/-- The restriction of a complex-linear map commuting with `σ` to `J_T`. -/
def restrictLinear (M : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ)
    (hσ : ∀ x, compactInvolution (M x) = M (compactInvolution x)) :
    CompactTits →ₗ[ℝ] CompactTits where
  toFun x := CompactTits.ofFixed (M (CompactTits.coordinates x)) (by
    rw [hσ, CompactTits.fixed])
  map_add' x y := CompactTits.ext (by simp)
  map_smul' r x := CompactTits.ext (by
    simp only [CompactTits.coordinates_ofFixed, map_smul, RingHom.id_apply]
    exact LinearMap.map_smul_of_tower M r _)

@[simp] theorem restrictLinear_coordinates (M : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ) (hσ)
    (x : CompactTits) :
    CompactTits.coordinates (restrictLinear M hσ x) = M (CompactTits.coordinates x) := rfl

/-- The restriction of a `σ`-equivariant complex-linear bijection, as a real-linear equivalence. -/
def restrictEquiv (M M' : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ)
    (hσ : ∀ x, compactInvolution (M x) = M (compactInvolution x))
    (hσ' : ∀ x, compactInvolution (M' x) = M' (compactInvolution x))
    (h₁ : ∀ x, M' (M x) = x) (h₂ : ∀ x, M (M' x) = x) : CompactTits ≃ₗ[ℝ] CompactTits :=
  { restrictLinear M hσ with
    invFun := restrictLinear M' hσ'
    left_inv := fun x => CompactTits.ext (by simp [h₁])
    right_inv := fun x => CompactTits.ext (by simp [h₂]) }

@[simp] theorem restrictEquiv_coordinates (M M' : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ) (hσ hσ' h₁ h₂)
    (x : CompactTits) :
    CompactTits.coordinates (restrictEquiv M M' hσ hσ' h₁ h₂ x) = M (CompactTits.coordinates x) :=
  rfl

/-- A square-preserving restriction is an automorphism of `J_T`. -/
theorem isTitsAutomorphism_of_coordinates (f : CompactTits ≃ₗ[ℝ] CompactTits)
    (M : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ)
    (hf : ∀ x, CompactTits.coordinates (f x) = M (CompactTits.coordinates x))
    (hM : ∀ z, M (firstTitsSquare z) = firstTitsSquare (M z)) : IsTitsAutomorphism f := by
  intro x y
  apply CompactTits.ext
  rw [hf, coordinates_product, coordinates_product, hf, hf, map_firstTitsJordanProduct_of_square M hM]

/-! ## Matrix facts -/

theorem unitary_conjTranspose_mul {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    Uᴴ * U = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

theorem unitary_mul_conjTranspose {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    U * Uᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU

theorem unitary_conjTranspose_mem {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem hU

theorem adjugate_of_unitary {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    Matrix.adjugate U = U.det • Uᴴ := by
  have h := congrArg (fun M => Uᴴ * M) (Matrix.mul_adjugate U)
  simp only [← Matrix.mul_assoc, unitary_conjTranspose_mul hU, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one] at h
  exact h

theorem det_mul_det_conjTranspose {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    U.det * (Uᴴ).det = 1 := by
  rw [← Matrix.det_mul, unitary_mul_conjTranspose hU, Matrix.det_one]

theorem trace3_conj {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (M : Mat3 ℂ) :
    trace3 (U * M * Uᴴ) = trace3 M := by
  rw [trace3_eq_matrixTrace, trace3_eq_matrixTrace, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    unitary_conjTranspose_mul hU, Matrix.one_mul]

theorem conj_mul {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (M N : Mat3 ℂ) :
    U * M * Uᴴ * (U * N * Uᴴ) = U * (M * N) * Uᴴ := by
  calc U * M * Uᴴ * (U * N * Uᴴ) = U * M * (Uᴴ * U) * N * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (M * N) * Uᴴ := by rw [unitary_conjTranspose_mul hU]; simp only [Matrix.mul_one,
      Matrix.mul_assoc]

theorem adjugate3_conj {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) (M : Mat3 ℂ) :
    adjugate3 (U * M * Uᴴ) = U * adjugate3 M * Uᴴ := by
  simp only [AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate,
    Matrix.adjugate_mul_distrib, adjugate_of_unitary hU,
    adjugate_of_unitary (unitary_conjTranspose_mem hU), Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [det_mul_det_conjTranspose hU, one_smul]

/-- For `R ∈ SU(3)`, `adj R = R*`. -/
theorem adjugate_of_specialUnitary {R : Mat3 ℂ} (hR : R ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    Matrix.adjugate R = Rᴴ := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hR
  rw [adjugate_of_unitary hR.1, hR.2, one_smul]

theorem specialUnitary_conjTranspose_mem {R : Mat3 ℂ}
    (hR : R ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    Rᴴ ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hR ⊢
  refine ⟨unitary_conjTranspose_mem hR.1, ?_⟩
  rw [Matrix.det_conjTranspose, hR.2, star_one]

end

end ThirteenPlanes.AlbertGrading
