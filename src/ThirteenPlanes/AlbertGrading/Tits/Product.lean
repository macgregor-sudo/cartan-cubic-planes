module

public import ThirteenPlanes.AlbertGrading.Tits.Statements
public import ThirteenPlanes.Tits.TitsSquare

@[expose] public section

set_option backward.privateInPublic true

/-! The explicit first Tits Jordan product.

The term-by-term product `paperProduct` equals `polarProduct firstTitsSquare`.
The compact real form inherits this product in first Tits coordinates. -/

open scoped Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-- `½ (adj(a+b) − adj a − adj b) = ½ a # b`, entrywise. -/
theorem adjugate3_polar (a b : Mat3 ℂ) :
    adjugate3 (a + b) - adjugate3 a - adjugate3 b = sharpPair a b := by
  ext i j
  simp only [Matrix.sub_apply, sharpPair, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_three, trace3, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [adjugate3] <;> ring

private theorem trace3_add (a b : Mat3 ℂ) : trace3 (a + b) = trace3 a + trace3 b := by
  simp only [trace3, Matrix.add_apply]; ring

theorem firstTitsJordanProduct_eq_polar (x y : FirstTits ℂ) :
    firstTitsJordanProduct x y = polarProduct firstTitsSquare x y := by
  rcases x with ⟨A, B, C⟩
  rcases y with ⟨A', B', C'⟩
  have h2 : (⅟(2 : ℂ)) = (1 / 2 : ℂ) := by rw [invOf_eq_inv]; norm_num
  simp only [polarProduct, firstTitsSquare, firstTitsJordanProduct, Prod.mk_add_mk, Prod.mk_sub_mk,
    Prod.smul_mk, h2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [trace3_add, add_mul, mul_add, add_smul]
    simp only [smul_sub, smul_add, smul_smul]
    module
  · have hp := adjugate3_polar C C'
    have hq : adjugate3 (C + C') = sharpPair C C' + adjugate3 C + adjugate3 C' := by
      rw [← hp]; abel
    simp only [hq, trace3_add, add_mul, mul_add, add_smul, smul_add, smul_sub, smul_smul]
    module
  · have hp := adjugate3_polar B B'
    have hq : adjugate3 (B + B') = sharpPair B B' + adjugate3 B + adjugate3 B' := by
      rw [← hp]; abel
    simp only [hq, trace3_add, add_mul, mul_add, add_smul, smul_add, smul_sub, smul_smul]
    module

theorem coordinates_product (x y : CompactTits) :
    CompactTits.coordinates (CompactTits.product x y) =
      firstTitsJordanProduct (CompactTits.coordinates x) (CompactTits.coordinates y) := by
  rw [firstTitsJordanProduct_eq_polar, CompactTits.coordinates_product_eq_polar]

/-- The diagonal of the polarized product is the square. -/
theorem polar_self (z : FirstTits ℂ) : polarProduct firstTitsSquare z z = firstTitsSquare z :=
  AlbertLean.Generic.TitsLinear.toTau.injective (by
    rw [AlbertLean.Generic.TitsSquare.toTau_polarProduct,
      AlbertLean.Generic.TitsSquare.toTau_firstTitsSquare])

theorem firstTitsJordanProduct_self (z : FirstTits ℂ) : firstTitsJordanProduct z z = firstTitsSquare z := by
  rw [firstTitsJordanProduct_eq_polar, polar_self]

/-- A complex-linear map preserving the square preserves the polarized product. -/
theorem map_polar_of_square (M : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ)
    (hM : ∀ z, M (firstTitsSquare z) = firstTitsSquare (M z)) (x y : FirstTits ℂ) :
    M (polarProduct firstTitsSquare x y) = polarProduct firstTitsSquare (M x) (M y) := by
  simp only [polarProduct, map_smul, map_sub, hM, map_add]

theorem map_firstTitsJordanProduct_of_square (M : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ)
    (hM : ∀ z, M (firstTitsSquare z) = firstTitsSquare (M z)) (x y : FirstTits ℂ) :
    M (firstTitsJordanProduct x y) = firstTitsJordanProduct (M x) (M y) := by
  simp only [firstTitsJordanProduct_eq_polar, map_polar_of_square M hM]

/-- `σ` is conjugate-linear and preserves the product: `σ(x ∘ y) = σx ∘ σy`. -/
theorem compactInvolution_firstTitsJordanProduct (x y : FirstTits ℂ) :
    compactInvolution (firstTitsJordanProduct x y) =
      firstTitsJordanProduct (compactInvolution x) (compactInvolution y) := by
  simp only [firstTitsJordanProduct_eq_polar, polarProduct, compactInvolution_complex_smul, map_sub,
    compactInvolution_square, map_add]
  congr 1
  rw [invOf_eq_inv]
  simp

end

end ThirteenPlanes.AlbertGrading
