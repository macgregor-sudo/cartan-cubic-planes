module

public import ThirteenPlanes.SignedProduct

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes

/-- Coefficient of the complex-bilinear trace metric in the full charge basis. -/
def gradeMetric (x y : Charge) : ℂ := if x + y = 0 then 3 else 0

/-- The equal-strength trace cubic restricted to three nonzero grades. -/
noncomputable def signedCoefficient (x y z : NonzeroCharge) : ℂ :=
  gradedProductCoefficient x.val y.val * gradeMetric (x.val + y.val) z.val

theorem dependentGrades_comm (x y : Charge) : dependentGrades x y ↔ dependentGrades y x := by
  unfold dependentGrades
  have hn : x = -y ↔ y = -x := by
    constructor <;> intro h <;> simp [h]
  tauto

theorem gradedProductCoefficient_comm (x y : Charge) :
    gradedProductCoefficient x y = gradedProductCoefficient y x := by
  classical
  simp only [gradedProductCoefficient, dependentGrades_comm x y, gradeExponent_comm x y]

theorem signedCoefficient_swap_first (x y z : NonzeroCharge) :
    signedCoefficient x y z = signedCoefficient y x z := by
  simp only [signedCoefficient, gradedProductCoefficient_comm x.val y.val, add_comm x.val y.val]

theorem gradeExponent_on_third (x y : Charge) :
    gradeExponent y (-x-y) = gradeExponent x y := by
  unfold gradeExponent
  simp only [Pi.sub_apply, Pi.neg_apply]
  linear_combination (y 0 * x 1 * y 2 - y 1 * x 0 * y 2) * (by decide : (3 : ZMod 3) = 0)

private theorem neg_sub_self (x : Charge) : -x - x = x := by
  funext i
  change -(x i) - x i = x i
  linear_combination -(x i) * (by decide : (3 : ZMod 3) = 0)

theorem signedCoefficient_cycle (x y z : NonzeroCharge) :
    signedCoefficient x y z = signedCoefficient y z x := by
  classical
  by_cases hz : x.val + y.val + z.val = 0
  · have hz' : y.val + z.val + x.val = 0 := by simpa only [add_assoc, add_comm, add_left_comm] using hz
    have he : z.val = -x.val - y.val := by linear_combination hz
    have ex : gradeExponent x.val y.val = gradeExponent y.val z.val := by
      rw [he, gradeExponent_on_third]
    have xy : x.val ≠ -y.val := by
      intro h
      apply z.property
      rw [he, h]
      abel
    have yz : y.val ≠ -z.val := by
      intro h
      apply x.property
      simpa [h, add_assoc] using hz
    have eqs : x.val = y.val ↔ y.val = z.val := by
      constructor
      · intro h
        rw [he, h, neg_sub_self]
      · intro h
        have hx : x.val = -z.val - z.val := by rw [h] at hz; linear_combination hz
        rw [hx, neg_sub_self, h]
    have hd : dependentGrades x.val y.val ↔ dependentGrades y.val z.val := by
      simp only [dependentGrades, x.property, y.property, z.property, xy, yz, false_or, or_false, eqs]
    simp only [signedCoefficient, gradeMetric, hz, hz', ↓reduceIte, gradedProductCoefficient, hd, ex]
  · have hz' : y.val + z.val + x.val ≠ 0 := by simpa only [add_assoc, add_comm, add_left_comm] using hz
    simp [signedCoefficient, gradeMetric, hz, hz']

end ThirteenPlanes
