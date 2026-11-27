module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import ThirteenPlanes.SignedProduct

@[expose] public section

set_option backward.privateInPublic true

/-! The phase condition for lifting a relabeling of the charges, its solution for every matrix of
determinant one over the field with three elements, and uniqueness up to a linear function.
Pure arithmetic over `ZMod 3`. -/

open Matrix

namespace ThirteenPlanes

namespace FiniteGroup

/-- Three-by-three matrices acting on the charges. -/
abbrev ChargeMatrix := Matrix (Fin 3) (Fin 3) (ZMod 3)

/-- An odd phase function. -/
def IsOddPhase (F : Charge → ZMod 3) : Prop := ∀ x, F (-x) = -F x

/-- The lifting condition on independent pairs of grades. -/
def LiftCondition (A : ChargeMatrix) (F : Charge → ZMod 3) : Prop :=
  ∀ x y : Charge, ¬ dependentGrades x y →
    F x + F y - F (x + y) = gradeExponent x y - gradeExponent (A *ᵥ x) (A *ᵥ y)

/-- The lifting condition on all pairs of grades. -/
def LiftConditionAll (A : ChargeMatrix) (F : Charge → ZMod 3) : Prop :=
  ∀ x y : Charge, F x + F y - F (x + y) = gradeExponent x y - gradeExponent (A *ᵥ x) (A *ᵥ y)

private theorem three_eq_zero : (3 : ZMod 3) = 0 := by decide

theorem IsOddPhase.map_zero {F : Charge → ZMod 3} (hF : IsOddPhase F) : F 0 = 0 := by
  have h := hF 0
  rw [neg_zero] at h
  linear_combination -h + F 0 * three_eq_zero

private theorem charge_two (x : Charge) : x + x = -x := by
  funext i
  change x i + x i = -(x i)
  linear_combination x i * three_eq_zero

private theorem gradeExponent_self (x : Charge) : gradeExponent x x = 0 := by
  unfold gradeExponent; ring

private theorem gradeExponent_neg_left (y : Charge) : gradeExponent (-y) y = 0 := by
  unfold gradeExponent; simp only [Pi.neg_apply]; ring

private theorem gradeExponent_zero_left (y : Charge) : gradeExponent 0 y = 0 := by
  unfold gradeExponent; simp

private theorem gradeExponent_zero_right (y : Charge) : gradeExponent y 0 = 0 := by
  unfold gradeExponent; simp

/-- For odd phases the condition on independent pairs extends to all pairs. -/
theorem LiftCondition.all {A : ChargeMatrix} {F : Charge → ZMod 3} (hF : IsOddPhase F)
    (h : LiftCondition A F) : LiftConditionAll A F := by
  intro x y
  by_cases hd : dependentGrades x y
  · rcases hd with rfl | rfl | rfl | rfl
    · simp [hF.map_zero, gradeExponent_zero_left]
    · simp [hF.map_zero, gradeExponent_zero_right]
    · rw [charge_two, hF, gradeExponent_self, gradeExponent_self]
      linear_combination F x * three_eq_zero
    · rw [neg_add_cancel, hF, hF.map_zero, Matrix.mulVec_neg, gradeExponent_neg_left,
        gradeExponent_neg_left]
      ring
  · exact h x y hd

theorem LiftConditionAll.lift {A : ChargeMatrix} {F : Charge → ZMod 3}
    (h : LiftConditionAll A F) : LiftCondition A F := fun x y _ => h x y

/-- Lifts compose. -/
theorem LiftConditionAll.mul {A B : ChargeMatrix} {F G : Charge → ZMod 3}
    (hA : LiftConditionAll A F) (hB : LiftConditionAll B G) :
    LiftConditionAll (A * B) (fun x => G x + F (B *ᵥ x)) := by
  intro x y
  simp only [Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
  linear_combination hB x y + hA (B *ᵥ x) (B *ᵥ y)

theorem IsOddPhase.comp {B : ChargeMatrix} {F G : Charge → ZMod 3} (hF : IsOddPhase F)
    (hG : IsOddPhase G) : IsOddPhase (fun x => G x + F (B *ᵥ x)) := by
  intro x
  simp only [Matrix.mulVec_neg]
  rw [hG, hF]
  ring

private theorem isOddPhase_zero : IsOddPhase (fun _ => 0) := fun _ => by simp

private theorem diagonal_lift (d : Fin 3 → ZMod 3) (hd : (diagonal d).det = 1) :
    LiftConditionAll (diagonal d) (fun _ => 0) := by
  intro x y
  rw [Matrix.det_diagonal, Fin.prod_univ_three] at hd
  simp only [Matrix.mulVec_diagonal, gradeExponent]
  linear_combination (x 0 * y 1 - x 1 * y 0) * (y 2 - x 2) * hd

private theorem transvection_mulVec (i j : Fin 3) (c : ZMod 3) (x : Charge) (k : Fin 3) :
    (transvection i j c *ᵥ x) k = x k + if k = i then c * x j else 0 := by
  simp [transvection, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]

/-- The six elementary transvections with entry one have explicit odd lifts. -/
private theorem transvection_one_lift (i j : Fin 3) (hij : i ≠ j) :
    ∃ F, IsOddPhase F ∧ LiftConditionAll (transvection i j 1) F := by
  fin_cases i <;> fin_cases j <;> simp at hij
  · -- (a,b,c) ↦ (a+b,b,c)
    refine ⟨fun _ => 0, isOddPhase_zero, fun x y => ?_⟩
    simp only [gradeExponent, transvection_mulVec]
    simp
    ring
  · -- (a,b,c) ↦ (a+c,b,c)
    refine ⟨fun x => -(x 1 * x 2 ^ 2), fun x => by simp, fun x y => ?_⟩
    simp only [gradeExponent, transvection_mulVec]
    simp
    linear_combination (x 1 * x 2 * y 2 + x 2 * y 1 * y 2) * three_eq_zero
  · -- (a,b,c) ↦ (a,b+a,c)
    refine ⟨fun _ => 0, isOddPhase_zero, fun x y => ?_⟩
    simp only [gradeExponent, transvection_mulVec]
    simp
    ring
  · -- (a,b,c) ↦ (a,b+c,c)
    refine ⟨fun x => x 0 * x 2 ^ 2, fun x => by simp, fun x y => ?_⟩
    simp only [gradeExponent, transvection_mulVec]
    simp
    linear_combination (-(x 0 * x 2 * y 2) - x 2 * y 0 * y 2) * three_eq_zero
  · -- (a,b,c) ↦ (a,b,c+a)
    refine ⟨fun x => -(x 0 ^ 2 * x 1), fun x => by simp, fun x y => ?_⟩
    simp only [gradeExponent, transvection_mulVec]
    simp
    linear_combination (x 0 * x 1 * y 0 + x 0 * y 0 * y 1) * three_eq_zero
  · -- (a,b,c) ↦ (a,b,c+b)
    refine ⟨fun x => x 0 * x 1 ^ 2, fun x => by simp, fun x y => ?_⟩
    simp only [gradeExponent, transvection_mulVec]
    simp
    linear_combination (-(x 0 * x 1 * y 1) - x 1 * y 0 * y 1) * three_eq_zero

private theorem transvection_lift (t : TransvectionStruct (Fin 3) (ZMod 3)) :
    ∃ F, IsOddPhase F ∧ LiftConditionAll t.toMatrix F := by
  obtain ⟨i, j, hij, c⟩ := t
  change ∃ F, IsOddPhase F ∧ LiftConditionAll (transvection i j c) F
  obtain ⟨F, hFo, hF⟩ := transvection_one_lift i j hij
  fin_cases c
  · change ∃ F, IsOddPhase F ∧ LiftConditionAll (transvection i j (0 : ZMod 3)) F
    rw [transvection_zero]
    exact ⟨fun _ => 0, isOddPhase_zero, fun x y => by simp⟩
  · exact ⟨F, hFo, hF⟩
  · have e : transvection i j (2 : ZMod 3) = transvection i j 1 * transvection i j 1 := by
      rw [transvection_mul_transvection_same i j hij]; rfl
    change ∃ F, IsOddPhase F ∧ LiftConditionAll (transvection i j (2 : ZMod 3)) F
    rw [e]
    exact ⟨_, hFo.comp hFo, hF.mul hF⟩

/-- Every determinant-one matrix over the field with three elements has an odd lift. -/
theorem exists_lift (A : SpecialLinearGroup (Fin 3) (ZMod 3)) :
    ∃ F, IsOddPhase F ∧ LiftCondition A F := by
  suffices h : ∃ F, IsOddPhase F ∧ LiftConditionAll (A : ChargeMatrix) F by
    obtain ⟨F, hF, hl⟩ := h
    exact ⟨F, hF, hl.lift⟩
  refine diagonal_transvection_induction
    (fun M => ∃ F, IsOddPhase F ∧ LiftConditionAll M F) (A : ChargeMatrix) ?_ ?_ ?_
  · intro D hD
    rw [A.property] at hD
    exact ⟨fun _ => 0, isOddPhase_zero, diagonal_lift D hD⟩
  · exact transvection_lift
  · rintro M N ⟨F, hFo, hF⟩ ⟨G, hGo, hG⟩
    exact ⟨_, hFo.comp hGo, hF.mul hG⟩

/-- Two odd lifts of the same matrix differ by a linear function. -/
theorem lift_unique {A : ChargeMatrix} {F F' : Charge → ZMod 3} (hF : IsOddPhase F)
    (hF' : IsOddPhase F') (h : LiftCondition A F) (h' : LiftCondition A F') :
    ∃ χ : Charge, ∀ x, F' x = F x + ∑ i, χ i * x i := by
  set G : Charge → ZMod 3 := fun x => F' x - F x with hG
  have hadd : ∀ x y, G (x + y) = G x + G y := by
    intro x y
    have e := h.all hF x y
    have e' := h'.all hF' x y
    simp only [hG]
    linear_combination e - e'
  let Gh : Charge →+ ZMod 3 := AddMonoidHom.mk' G hadd
  have hsmul : ∀ (c : ZMod 3) (v : Charge), G (c • v) = c * G v := by
    intro c v
    fin_cases c
    · have := hadd 0 0
      simp only [add_zero] at this
      change G (0 • v) = 0 * G v
      rw [zero_smul, zero_mul]
      linear_combination -this
    · change G ((1 : ZMod 3) • v) = 1 * G v
      rw [one_smul, one_mul]
    · change G ((2 : ZMod 3) • v) = 2 * G v
      rw [two_smul, hadd]
      ring
  refine ⟨fun i => G (Pi.single i 1), fun x => ?_⟩
  have hx : x = ∑ i, x i • (Pi.single i 1 : Charge) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hGx : G x = ∑ i, x i * G (Pi.single i 1) := by
    conv_lhs => rw [hx]
    change Gh (∑ i, x i • (Pi.single i 1 : Charge)) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have : F' x = F x + G x := by simp only [hG]; ring
  rw [this, hGx]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end FiniteGroup

end ThirteenPlanes
