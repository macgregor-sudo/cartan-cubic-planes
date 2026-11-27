module

public import ThirteenPlanes.AlbertGrading.Tits.GradingGroup
public import ThirteenPlanes.AlbertGrading.Tits.NonVacuity

@[expose] public section

/-! The ternary grading and exterior frame in first Tits coordinates.

The compact involution preserves the product. The explicit first Tits product agrees with
the polarized square, and the exterior frame has the prescribed contrast. -/

namespace ThirteenPlanes.AlbertGrading

/-- First-Tits grading and Weyl basis. -/
/- For the ternary Albert grading in first-Tits coordinates, see C. Draper Fontanals
and C. Martín González (arXiv:math/0703840, §3.4) and Elduque and Kochetov
(§4.5, Theorem 4.8). This construction checks the action and graded products explicitly. -/
theorem titsLemma : Statements.TitsLemma :=
  ⟨fun _ hU => adPart hU, phiPart, fun _ hR => psiPart hR, titsBasis_zero, titsBasis_involution,
    titsBasis_traceForm, titsBasis_product_dependent, titsBasis_product_independent, partThree⟩

/-- The contrast of the exterior frame is `ι₂(1) = u_{(0,0,2)}`, in the basis of the first-Tits grading and Weyl basis (ii). -/
theorem exteriorPoint_contrast_eq_titsBasis :
    titsContrast exteriorPoint = titsBasis (chargeFrom 0 2) := by
  have hw : weylMatrix 0 = (1 : Matrix (ZMod 3) (ZMod 3) ℂ) := by
    ext i j; simp [weylMatrix, Matrix.one_apply]
  rw [exteriorPoint_contrast, titsBasis, weylD_eq_weylMatrix]
  have h : ((chargeFrom 0 2 0, chargeFrom 0 2 1) : WeylLabel) = 0 := rfl
  rw [h, hw]
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  simp [iota, chargeFrom, h20, h21]
  rfl

end ThirteenPlanes.AlbertGrading
