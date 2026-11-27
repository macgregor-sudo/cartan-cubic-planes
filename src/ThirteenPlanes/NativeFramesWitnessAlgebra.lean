/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Glennie.Native
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Exact rational-square-root coefficients and the native Albert bridge

The coefficient algebra is the computable pair model r+s√3. Its evaluation
homomorphism is proved using √3²=3. The coefficient six-slot product is linked
to the native Jordan product by its coordinate formulas;
the finite coefficient checks give literal native equations.
Mathlib's QuadraticAlgebra is imported at the pinned revision, Apache-2.0.
-/

@[expose] public section

namespace ThirteenPlanes.NativeWitness.ExactAlgebra

set_option maxHeartbeats 2000000

/-- Computable exact pairs; no field or irreducibility instance is needed. -/
abbrev Coeff := QuadraticAlgebra ℚ 3 0

/-- Rational constants use the canonical algebra map, including all denominators. -/
def rational (q : ℚ) : Coeff := algebraMap ℚ Coeff q

noncomputable def evaluate : Coeff →+* ℝ :=
  (QuadraticAlgebra.lift (R := ℚ) (a := 3) (b := 0)
    ⟨Real.sqrt 3, by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      norm_num [pow_two] at h ⊢⟩).toRingHom

@[simp] theorem evaluate_rational (q : ℚ) : evaluate (rational q) = (q : ℝ) := by
  exact (QuadraticAlgebra.lift (R := ℚ) (a := 3) (b := 0)
    ⟨Real.sqrt 3, by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      norm_num [pow_two] at h ⊢⟩).commutes q

@[simp] theorem evaluate_mk (a b : ℚ) : evaluate ⟨a,b⟩ = (a : ℝ) + (b : ℝ)*Real.sqrt 3 := by
  simp [evaluate,QuadraticAlgebra.lift_apply_apply,Algebra.smul_def]

abbrev ExactQuaternion := Quaternion Coeff
abbrev ExactOctonion := ExactQuaternion × ExactQuaternion

instance : DecidableEq ExactQuaternion := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.imI = y.imI ∧ x.imJ = y.imJ ∧ x.imK = y.imK)
    QuaternionAlgebra.ext_iff.symm

noncomputable def evaluateQuaternion (x : ExactQuaternion) : Quaternion ℝ :=
  ⟨evaluate x.re,evaluate x.imI,evaluate x.imJ,evaluate x.imK⟩

@[simp] theorem evaluateQuaternion_add (x y : ExactQuaternion) :
    evaluateQuaternion (x+y) = evaluateQuaternion x + evaluateQuaternion y := by
  apply Quaternion.ext <;> simp [evaluateQuaternion]

@[simp] theorem evaluateQuaternion_neg (x : ExactQuaternion) :
    evaluateQuaternion (-x) = -evaluateQuaternion x := by
  apply Quaternion.ext <;> simp [evaluateQuaternion]

@[simp] theorem evaluateQuaternion_sub (x y : ExactQuaternion) :
    evaluateQuaternion (x-y) = evaluateQuaternion x - evaluateQuaternion y := by
  apply Quaternion.ext <;> simp [evaluateQuaternion]

@[simp] theorem evaluateQuaternion_mul (x y : ExactQuaternion) :
    evaluateQuaternion (x*y) = evaluateQuaternion x * evaluateQuaternion y := by
  apply Quaternion.ext <;>
    simp [evaluateQuaternion, map_add, map_mul, sub_eq_add_neg]

@[simp] theorem evaluateQuaternion_star (x : ExactQuaternion) :
    evaluateQuaternion (star x) = star (evaluateQuaternion x) := by
  apply Quaternion.ext <;> simp [evaluateQuaternion]

@[simp] theorem evaluateQuaternion_smul (r : Coeff) (x : ExactQuaternion) :
    evaluateQuaternion (r • x) = evaluate r • evaluateQuaternion x := by
  apply Quaternion.ext <;> simp [evaluateQuaternion,smul_eq_mul,map_mul]

noncomputable def evaluateOctonion (x : ExactOctonion) : Glennie.Octonion :=
  (evaluateQuaternion x.1,evaluateQuaternion x.2)

@[simp] theorem evaluateOctonion_add (x y : ExactOctonion) :
    evaluateOctonion (x+y) = evaluateOctonion x + evaluateOctonion y := by
  apply Prod.ext <;> simp [evaluateOctonion]

@[simp] theorem evaluateOctonion_neg (x : ExactOctonion) :
    evaluateOctonion (-x) = -evaluateOctonion x := by
  apply Prod.ext <;> simp [evaluateOctonion]

@[simp] theorem evaluateOctonion_zero : evaluateOctonion 0 = 0 := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [evaluateOctonion,evaluateQuaternion]

@[simp] theorem evaluateOctonion_smul (r : Coeff) (x : ExactOctonion) :
    evaluateOctonion (r • x) = evaluate r • evaluateOctonion x := by
  apply Prod.ext <;> simp [evaluateOctonion]

def octMul (x y : ExactOctonion) : ExactOctonion :=
  (x.1*y.1-star y.2*x.2,y.2*x.1+x.2*star y.1)

def octConj (x : ExactOctonion) : ExactOctonion := (star x.1,-x.2)

def octDot (x y : ExactOctonion) : Coeff := (octMul x (octConj y)).1.re

@[simp] theorem evaluate_octMul (x y : ExactOctonion) :
    evaluateOctonion (octMul x y) = Glennie.octMul (evaluateOctonion x) (evaluateOctonion y) := by
  apply Prod.ext <;> simp [octMul,Glennie.octMul,evaluateOctonion]

@[simp] theorem evaluate_octConj (x : ExactOctonion) :
    evaluateOctonion (octConj x) = Glennie.octConj (evaluateOctonion x) := by
  apply Prod.ext <;> simp [octConj,Glennie.octConj,evaluateOctonion]

@[simp] theorem evaluate_octDot (x y : ExactOctonion) :
    evaluate (octDot x y) = Glennie.octDot (evaluateOctonion x) (evaluateOctonion y) := by
  have h := evaluate_octMul x (octConj y)
  rw [evaluate_octConj] at h
  exact congrArg (fun z : Glennie.Octonion => z.1.re) h

/-- Exact six-slot coordinate data; the native carrier remains Glennie.Albert. -/
structure Element where
  d0 : Coeff
  d1 : Coeff
  d2 : Coeff
  o01 : ExactOctonion
  o02 : ExactOctonion
  o12 : ExactOctonion
  deriving DecidableEq

instance instZeroElement : Zero Element := ⟨⟨0,0,0,0,0,0⟩⟩
instance instOneElement : One Element := ⟨⟨1,1,1,0,0,0⟩⟩
instance instAddElement : Add Element := ⟨fun x y => ⟨x.d0+y.d0,x.d1+y.d1,x.d2+y.d2,
  x.o01+y.o01,x.o02+y.o02,x.o12+y.o12⟩⟩

namespace Element
@[simp] theorem zero_d0 : (0 : Element).d0 = 0 := rfl
@[simp] theorem one_d0 : (1 : Element).d0 = 1 := rfl
@[simp] theorem add_d0 (x y : Element) : (x+y).d0 = x.d0+y.d0 := rfl
@[simp] theorem zero_d1 : (0 : Element).d1 = 0 := rfl
@[simp] theorem one_d1 : (1 : Element).d1 = 1 := rfl
@[simp] theorem add_d1 (x y : Element) : (x+y).d1 = x.d1+y.d1 := rfl
@[simp] theorem zero_d2 : (0 : Element).d2 = 0 := rfl
@[simp] theorem one_d2 : (1 : Element).d2 = 1 := rfl
@[simp] theorem add_d2 (x y : Element) : (x+y).d2 = x.d2+y.d2 := rfl
@[simp] theorem zero_o01 : (0 : Element).o01 = 0 := rfl
@[simp] theorem one_o01 : (1 : Element).o01 = 0 := rfl
@[simp] theorem add_o01 (x y : Element) : (x+y).o01 = x.o01+y.o01 := rfl
@[simp] theorem zero_o02 : (0 : Element).o02 = 0 := rfl
@[simp] theorem one_o02 : (1 : Element).o02 = 0 := rfl
@[simp] theorem add_o02 (x y : Element) : (x+y).o02 = x.o02+y.o02 := rfl
@[simp] theorem zero_o12 : (0 : Element).o12 = 0 := rfl
@[simp] theorem one_o12 : (1 : Element).o12 = 0 := rfl
@[simp] theorem add_o12 (x y : Element) : (x+y).o12 = x.o12+y.o12 := rfl
end Element

noncomputable def evaluateElement (x : Element) : Glennie.Albert :=
  ⟨evaluate x.d0,evaluate x.d1,evaluate x.d2,
    evaluateOctonion x.o01,evaluateOctonion x.o02,evaluateOctonion x.o12⟩

def trace (x : Element) : Coeff := x.d0+x.d1+x.d2

/-- Literal coordinate polynomial for the same half Jordan product. -/
def jordan (x y : Element) : Element :=
  ⟨x.d0*y.d0+octDot x.o01 y.o01+octDot x.o02 y.o02,
   x.d1*y.d1+octDot x.o01 y.o01+octDot x.o12 y.o12,
   x.d2*y.d2+octDot x.o02 y.o02+octDot x.o12 y.o12,
   rational (1/2) • ((x.d0+x.d1) • y.o01+(y.d0+y.d1) • x.o01+
     octMul x.o02 (octConj y.o12)+octMul y.o02 (octConj x.o12)),
   rational (1/2) • ((x.d0+x.d2) • y.o02+(y.d0+y.d2) • x.o02+
     octMul x.o01 y.o12+octMul y.o01 x.o12),
   rational (1/2) • ((x.d1+x.d2) • y.o12+(y.d1+y.d2) • x.o12+
     octMul (octConj x.o01) y.o02+octMul (octConj y.o01) x.o02)⟩

def inner (x y : Element) : Coeff := trace (jordan x y)

@[simp] theorem evaluateElement_zero : evaluateElement 0 = 0 := by
  apply Glennie.Albert.ext <;> simp [evaluateElement]

@[simp] theorem evaluateElement_one : evaluateElement 1 = 1 := by
  apply Glennie.Albert.ext <;> simp [evaluateElement]

@[simp] theorem evaluateElement_add (x y : Element) :
    evaluateElement (x+y) = evaluateElement x + evaluateElement y := by
  apply Glennie.Albert.ext <;> simp [evaluateElement]

@[simp] theorem evaluate_trace (x : Element) :
    evaluate (trace x) = Glennie.trace (evaluateElement x) := by
  simp [trace,Glennie.trace,evaluateElement]

/-- Coefficient multiplication evaluates to the native Jordan product. -/
theorem evaluate_jordan (x y : Element) :
    evaluateElement (jordan x y) = Glennie.jordan (evaluateElement x) (evaluateElement y) := by
  apply Glennie.Albert.ext <;>
    simp [evaluateElement,jordan,Glennie.jordan_d0,Glennie.jordan_d1,Glennie.jordan_d2,
      Glennie.jordan_o01,Glennie.jordan_o02,Glennie.jordan_o12]

/-- Every exact coefficient pairing equation is a literal native trace-pairing equation. -/
theorem evaluate_inner (x y : Element) :
    evaluate (inner x y) = Glennie.inner (evaluateElement x) (evaluateElement y) := by
  unfold inner Glennie.inner
  rw [evaluate_trace,evaluate_jordan]

end ThirteenPlanes.NativeWitness.ExactAlgebra
