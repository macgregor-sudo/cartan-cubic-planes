module

public import ThirteenPlanes.AlbertGrading.Tits.Maps

@[expose] public section

set_option backward.privateInPublic true

/-! # first-Tits grading and Weyl basis (i) for the three families -/

open scoped Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

private theorem trace3_smul (c : ℂ) (M : Mat3 ℂ) : trace3 (c • M) = c * trace3 M := by
  simp only [trace3, Matrix.smul_apply, smul_eq_mul]; ring

private theorem adjugate3_smul (c : ℂ) (M : Mat3 ℂ) : adjugate3 (c • M) = c ^ 2 • adjugate3 M := by
  simp only [AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate, Matrix.adjugate_smul,
    Fintype.card_fin]

/-! ## `Ad_U` -/

def adLin (U : Mat3 ℂ) : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ where
  toFun := adMap U
  map_add' x y := by simp [adMap, Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp [adMap, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem adLin_apply (U : Mat3 ℂ) (x : FirstTits ℂ) : adLin U x = adMap U x := rfl

section Ad

variable {U : Mat3 ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ)
include hU

theorem adMap_one : adMap U firstTitsOne = firstTitsOne := by
  simp [adMap, firstTitsOne, unitary_mul_conjTranspose hU]

theorem adMap_square (z : FirstTits ℂ) :
    adMap U (firstTitsSquare z) = firstTitsSquare (adMap U z) := by
  rcases z with ⟨A, B, C⟩
  have h1 := unitary_mul_conjTranspose hU
  simp only [adMap, firstTitsSquare, conj_mul hU, adjugate3_conj hU, trace3_conj hU]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, h1]

theorem adMap_traceForm (x y : FirstTits ℂ) :
    titsTraceForm (adMap U x) (adMap U y) = titsTraceForm x y := by
  simp only [titsTraceForm, adMap, conj_mul hU, trace3_conj hU]

theorem adMap_involution (x : FirstTits ℂ) :
    compactInvolution (adMap U x) = adMap U (compactInvolution x) := by
  simp [adMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem adMap_cancel (x : FirstTits ℂ) : adMap Uᴴ (adMap U x) = x := by
  have h := unitary_conjTranspose_mul hU
  have hl (X : Mat3 ℂ) : Uᴴ * (U * X) = X := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  simp [adMap, Matrix.mul_assoc, hl, h]

theorem adPart :
    adMap U firstTitsOne = firstTitsOne ∧
    (∀ x y, titsTraceForm (adMap U x) (adMap U y) = titsTraceForm x y) ∧
    (∀ x y, adMap U (firstTitsJordanProduct x y) = firstTitsJordanProduct (adMap U x) (adMap U y)) ∧
    (∀ x, compactInvolution (adMap U x) = adMap U (compactInvolution x)) ∧
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
      ∀ x, CompactTits.coordinates (f x) = adMap U (CompactTits.coordinates x) := by
  have hU' := unitary_conjTranspose_mem hU
  have hUU : Uᴴᴴ = U := Matrix.conjTranspose_conjTranspose U
  refine ⟨adMap_one hU, adMap_traceForm hU,
    map_firstTitsJordanProduct_of_square (adLin U) (adMap_square hU), adMap_involution hU, ?_⟩
  let f := restrictEquiv (adLin U) (adLin Uᴴ) (adMap_involution hU) (adMap_involution hU')
    (adMap_cancel hU) (fun x => by simpa [hUU] using adMap_cancel hU' x)
  exact ⟨f, isTitsAutomorphism_of_coordinates f (adLin U) (fun _ => rfl) (adMap_square hU),
    fun _ => rfl⟩

end Ad

/-! ## `φ` -/

def phiLin : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ where
  toFun := phiMap
  map_add' x y := by simp [phiMap, smul_add]
  map_smul' c x := by simp [phiMap, smul_comm _ c]

@[simp] theorem phiLin_apply (x : FirstTits ℂ) : phiLin x = phiMap x := rfl

private theorem omega_mul_sq : chargeRoot * chargeRoot ^ 2 = 1 := by
  rw [← pow_succ', chargeRoot_cube]

private theorem sq_mul_omega : chargeRoot ^ 2 * chargeRoot = 1 := by
  rw [← pow_succ, chargeRoot_cube]

private theorem sq_sq_omega : (chargeRoot ^ 2) ^ 2 = chargeRoot := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, chargeRoot_cube, one_mul]

private theorem star_omega : star chargeRoot = chargeRoot ^ 2 := chargeRoot_sq_eq_star.symm

private theorem star_omega_sq : star (chargeRoot ^ 2) = chargeRoot := by
  rw [star_pow, star_omega, sq_sq_omega]

theorem phiMap_one : phiMap firstTitsOne = firstTitsOne := by simp [phiMap, firstTitsOne]

theorem phiMap_square (z : FirstTits ℂ) : phiMap (firstTitsSquare z) = firstTitsSquare (phiMap z) := by
  rcases z with ⟨A, B, C⟩
  simp only [phiMap, firstTitsSquare, adjugate3_smul, trace3_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, sq_sq_omega, omega_mul_sq, sq_mul_omega, one_smul, one_mul]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> module

theorem phiMap_traceForm (x y : FirstTits ℂ) :
    titsTraceForm (phiMap x) (phiMap y) = titsTraceForm x y := by
  simp only [titsTraceForm, phiMap, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace3_smul,
    omega_mul_sq, sq_mul_omega, one_mul]

theorem phiMap_involution (x : FirstTits ℂ) :
    compactInvolution (phiMap x) = phiMap (compactInvolution x) := by
  simp [phiMap, Matrix.conjTranspose_smul, star_omega, sq_sq_omega]

theorem phiMap_cancel (x : FirstTits ℂ) : phiMap (phiMap (phiMap x)) = x := by
  rcases x with ⟨A, B, C⟩
  simp only [phiMap, smul_smul]
  have h1 : chargeRoot * (chargeRoot * chargeRoot) = 1 := by
    rw [← chargeRoot_cube]; ring
  have h2 : chargeRoot ^ 2 * (chargeRoot ^ 2 * chargeRoot ^ 2) = 1 := by
    rw [show chargeRoot ^ 2 * (chargeRoot ^ 2 * chargeRoot ^ 2) = (chargeRoot ^ 3) ^ 2 by ring,
      chargeRoot_cube, one_pow]
  rw [h1, h2, one_smul, one_smul]

theorem phiPart :
    phiMap firstTitsOne = firstTitsOne ∧
    (∀ x y, titsTraceForm (phiMap x) (phiMap y) = titsTraceForm x y) ∧
    (∀ x y, phiMap (firstTitsJordanProduct x y) = firstTitsJordanProduct (phiMap x) (phiMap y)) ∧
    (∀ x, compactInvolution (phiMap x) = phiMap (compactInvolution x)) ∧
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
      ∀ x, CompactTits.coordinates (f x) = phiMap (CompactTits.coordinates x) := by
  refine ⟨phiMap_one, phiMap_traceForm, map_firstTitsJordanProduct_of_square phiLin phiMap_square,
    phiMap_involution, ?_⟩
  let f := restrictEquiv phiLin (phiLin.comp phiLin) phiMap_involution
    (fun x => by simp only [LinearMap.comp_apply, phiLin_apply, phiMap_involution]) (fun x => phiMap_cancel x) (fun x => phiMap_cancel x)
  exact ⟨f, isTitsAutomorphism_of_coordinates f phiLin (fun _ => rfl) phiMap_square,
    fun _ => rfl⟩

/-! ## `ψ_R` -/

def psiLin (R : Mat3 ℂ) : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ where
  toFun := psiMap R
  map_add' x y := by simp [psiMap, Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp [psiMap, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem psiLin_apply (R : Mat3 ℂ) (x : FirstTits ℂ) : psiLin R x = psiMap R x := rfl

section Psi

variable {R : Mat3 ℂ} (hR : R ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
include hR

theorem psiMap_one : psiMap R firstTitsOne = firstTitsOne := by simp [psiMap, firstTitsOne]

private theorem su_mul_star : R * Rᴴ = 1 :=
  unitary_mul_conjTranspose (Matrix.mem_specialUnitaryGroup_iff.mp hR).1

private theorem su_star_mul : Rᴴ * R = 1 :=
  unitary_conjTranspose_mul (Matrix.mem_specialUnitaryGroup_iff.mp hR).1

theorem psiMap_square (z : FirstTits ℂ) :
    psiMap R (firstTitsSquare z) = firstTitsSquare (psiMap R z) := by
  rcases z with ⟨A, B, C⟩
  have h1 := su_mul_star hR
  have hadjR : adjugate3 R = Rᴴ := by
    rw [AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate, adjugate_of_specialUnitary hR]
  have hadjR' : adjugate3 Rᴴ = R := by
    rw [AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate,
      adjugate_of_specialUnitary (specialUnitary_conjTranspose_mem hR),
      Matrix.conjTranspose_conjTranspose]
  have hBC : B * R * (Rᴴ * C) = B * C := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, h1, Matrix.one_mul]
  have hC : adjugate3 (Rᴴ * C) = adjugate3 C * R := by
    simp only [AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate,
      Matrix.adjugate_mul_distrib] at hadjR' ⊢
    rw [hadjR']
  have hB : adjugate3 (B * R) = Rᴴ * adjugate3 B := by
    simp only [AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate,
      Matrix.adjugate_mul_distrib] at hadjR ⊢
    rw [hadjR]
  simp only [psiMap, firstTitsSquare, hBC, hC, hB]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
  · simp [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]

theorem psiMap_traceForm (x y : FirstTits ℂ) :
    titsTraceForm (psiMap R x) (psiMap R y) = titsTraceForm x y := by
  have h1 := su_mul_star hR
  simp only [titsTraceForm, psiMap, trace3_eq_matrixTrace]
  rw [show x.2.1 * R * (Rᴴ * y.2.2) = x.2.1 * y.2.2 by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, h1, Matrix.one_mul],
    show Rᴴ * x.2.2 * (y.2.1 * R) = Rᴴ * (x.2.2 * y.2.1 * R) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm Rᴴ, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem psiMap_involution (x : FirstTits ℂ) :
    compactInvolution (psiMap R x) = psiMap R (compactInvolution x) := by
  simp [psiMap, Matrix.conjTranspose_mul]

theorem psiMap_cancel (x : FirstTits ℂ) : psiMap Rᴴ (psiMap R x) = x := by
  have h1 := su_mul_star hR
  simp [psiMap, Matrix.mul_assoc, h1, ← Matrix.mul_assoc R]

theorem psiPart :
    psiMap R firstTitsOne = firstTitsOne ∧
    (∀ x y, titsTraceForm (psiMap R x) (psiMap R y) = titsTraceForm x y) ∧
    (∀ x y, psiMap R (firstTitsJordanProduct x y) = firstTitsJordanProduct (psiMap R x) (psiMap R y)) ∧
    (∀ x, compactInvolution (psiMap R x) = psiMap R (compactInvolution x)) ∧
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
      ∀ x, CompactTits.coordinates (f x) = psiMap R (CompactTits.coordinates x) := by
  have hR' := specialUnitary_conjTranspose_mem hR
  have hRR : Rᴴᴴ = R := Matrix.conjTranspose_conjTranspose R
  refine ⟨psiMap_one hR, psiMap_traceForm hR,
    map_firstTitsJordanProduct_of_square (psiLin R) (psiMap_square hR), psiMap_involution hR, ?_⟩
  let f := restrictEquiv (psiLin R) (psiLin Rᴴ) (psiMap_involution hR) (psiMap_involution hR')
    (psiMap_cancel hR) (fun x => by simpa [hRR] using psiMap_cancel hR' x)
  exact ⟨f, isTitsAutomorphism_of_coordinates f (psiLin R) (fun _ => rfl) (psiMap_square hR),
    fun _ => rfl⟩

end Psi

end

end ThirteenPlanes.AlbertGrading
