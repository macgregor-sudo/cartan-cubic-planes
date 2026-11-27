module

public import ThirteenPlanes.SignedFields
public import Mathlib.Tactic

@[expose] public section

namespace ThirteenPlanes

noncomputable section

/-- The paper's cube root, with positive imaginary part. -/
def chargeRoot : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2

def gradeExponent (x y : Charge) : ZMod 3 :=
  (x 0 * y 1 - x 1 * y 0) * (y 2 - x 2)

/-- In the ternary grade space the scalar multiples of x are 0, x and -x. -/
def dependentGrades (x y : Charge) : Prop :=
  x = 0 ∨ y = 0 ∨ x = y ∨ x = -y

/-- Coefficient of the basis vector of grade x+y in the unital product. -/
def gradedProductCoefficient (x y : Charge) : ℂ := by
  classical
  exact if dependentGrades x y then 1 else -(chargeRoot ^ (gradeExponent x y).val) / 2

theorem gradeExponent_comm (x y : Charge) : gradeExponent x y = gradeExponent y x := by
  unfold gradeExponent
  ring

theorem gradedProductCoefficient_offLine :
    gradedProductCoefficient ![1,0,0] ![2,2,1] =
      (1 + Complex.I * (Real.sqrt 3 : ℝ)) / 4 := by
  have h : ¬ dependentGrades ![1,0,0] ![2,2,1] := by unfold dependentGrades; decide
  have e : (gradeExponent ![1,0,0] ![2,2,1]).val = 2 := by decide
  simp only [gradedProductCoefficient, h, ↓reduceIte, e, chargeRoot]
  have sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  linear_combination (norm := ring_nf) Complex.I ^ 2 / (-8 : ℂ) * sq -
    3 / 8 * Complex.I_sq

end
end ThirteenPlanes
