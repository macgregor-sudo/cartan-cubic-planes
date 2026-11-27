module

public import ThirteenPlanes.Cartan.GradedLineRestrictionNativeCore

@[expose] public section

set_option backward.privateInPublic true

/-! Complexification of arbitrary real derivations of the actual graded line. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading AlbertGrading.Grading.JC Module

noncomputable section

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex)

local notation "M" => albertGradingBasis hρ
local notation "L" => signedProjectiveLine l
local notation "Q" => lineAlgebraOf ρ l
local notation "Qc" => NormalizedTernaryBasis.gradedLineSubspace (albertGradingBasis hρ) (signedProjectiveLine l)
local notation "μ" => NormalizedTernaryBasis.gradedLineProduct (albertGradingBasis hρ) (signedProjectiveLine l)

include hρ in
/-- The underlying real graded line is closed under the actual Albert product. -/
theorem nativeGradedLine_productClosed (x y : Q) : Glennie.jordan x.val y.val ∈ Q := by
  apply (of_mem_gradedLineSubspace_iff hρ l _).mp
  rw [← of_mul]
  exact (M).gradedLine_productClosed L (of_mem_gradedLineSubspace_of_mem_lineAlgebra hρ l x.property)
    (of_mem_gradedLineSubspace_of_mem_lineAlgebra hρ l y.property)

private def realCoord (z : Qc) : Q :=
  ⟨z.val.re, re_mem_lineAlgebra_of_mem_gradedLineSubspace hρ l z.property⟩

private def imagCoord (z : Qc) : Q :=
  ⟨z.val.im, im_mem_lineAlgebra_of_mem_gradedLineSubspace hρ l z.property⟩

def ofLine (x : Q) : Qc :=
  ⟨of x.val, of_mem_gradedLineSubspace_of_mem_lineAlgebra hρ l x.property⟩

def realLineProduct (x y : Q) : Q :=
  ⟨Glennie.jordan x.val y.val, nativeGradedLine_productClosed hρ l x y⟩

@[simp] theorem ofLine_coe (x : Q) : (ofLine hρ l x).val = of x.val := rfl

/-- Extension acting separately on the real and imaginary coordinates of the actual line. -/
def extendGradedLineOperator (B : Module.End ℝ Q) : Module.End ℂ Qc where
  toFun z := ofLine hρ l (B (realCoord hρ l z)) + Complex.I • ofLine hρ l (B (imagCoord hρ l z))
  map_add' z w := by
    have hr : realCoord hρ l (z + w) = realCoord hρ l z + realCoord hρ l w := Subtype.ext rfl
    have hi : imagCoord hρ l (z + w) = imagCoord hρ l z + imagCoord hρ l w := Subtype.ext rfl
    apply Subtype.ext
    apply JC.ext <;> simp [ofLine_coe, hr, hi]
  map_smul' c z := by
    have hr : realCoord hρ l (c • z) = c.re • realCoord hρ l z - c.im • imagCoord hρ l z := Subtype.ext rfl
    have hi : imagCoord hρ l (c • z) = c.re • imagCoord hρ l z + c.im • realCoord hρ l z := Subtype.ext rfl
    apply Subtype.ext
    apply JC.ext <;> simp [ofLine_coe, hr, hi] <;> abel

@[simp] theorem extendGradedLineOperator_re (B : Module.End ℝ Q) (z : Qc) :
    (extendGradedLineOperator hρ l B z).val.re = (B (realCoord hρ l z)).val := by
  simp [extendGradedLineOperator, ofLine]

@[simp] theorem extendGradedLineOperator_im (B : Module.End ℝ Q) (z : Qc) :
    (extendGradedLineOperator hρ l B z).val.im = (B (imagCoord hρ l z)).val := by
  simp [extendGradedLineOperator, ofLine]

@[simp] theorem extendGradedLineOperator_of (B : Module.End ℝ Q) (x : Q) :
    (extendGradedLineOperator hρ l B (ofLine hρ l x)).val = of (B x).val := by
  have hr : realCoord hρ l (ofLine hρ l x) = x := Subtype.ext rfl
  have hi : imagCoord hρ l (ofLine hρ l x) = 0 := Subtype.ext rfl
  apply JC.ext <;> simp [hr, hi]

set_option maxHeartbeats 900000 in
/-- The arbitrary real Leibniz law extends to the actual complex product of the line. -/
theorem extendGradedLineOperator_mem_derivations (B : Module.End ℝ Q)
    (hB : ∀ x y : Q, (B (realLineProduct hρ l x y)).val =
      Glennie.jordan (B x).val y.val + Glennie.jordan x.val (B y).val) :
    extendGradedLineOperator hρ l B ∈ (M).gradedLineDerivations L := by
  apply ((M).mem_gradedLineDerivations L).mpr
  intro z w
  have hr : realCoord hρ l (μ z w) = realLineProduct hρ l (realCoord hρ l z) (realCoord hρ l w) -
      realLineProduct hρ l (imagCoord hρ l z) (imagCoord hρ l w) := Subtype.ext rfl
  have hi : imagCoord hρ l (μ z w) = realLineProduct hρ l (realCoord hρ l z) (imagCoord hρ l w) +
      realLineProduct hρ l (imagCoord hρ l z) (realCoord hρ l w) := Subtype.ext rfl
  apply Subtype.ext
  apply JC.ext
  · simp only [Submodule.coe_add, JC.add_re, (M).gradedLineProduct_coe, albertGradingBasis_product,
      JC.mul_re, extendGradedLineOperator_re, extendGradedLineOperator_im, hr, map_sub, Submodule.coe_sub, hB]
    simp only [realCoord, imagCoord]
    abel
  · simp only [Submodule.coe_add, JC.add_im, (M).gradedLineProduct_coe, albertGradingBasis_product,
      JC.mul_im, extendGradedLineOperator_re, extendGradedLineOperator_im, hi, map_add, Submodule.coe_add, hB]
    simp only [realCoord, imagCoord]
    abel

end

end ThirteenPlanes.Cartan
