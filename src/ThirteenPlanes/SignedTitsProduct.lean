module

public import ThirteenPlanes.SignedTitsCoordinates
public import Mathlib.Algebra.QuadraticAlgebra.Basic

@[expose] public section

set_option backward.privateInPublic true

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes

noncomputable section

/-- The individual Weyl vector in its homogeneous Tits component. -/
def homogeneousTits (x : Charge) : FirstTits ℂ :=
  let D : Mat3 ℂ := weylMatrix (x 0, x 1)
  (if x 2 = 0 then D else 0,
   if x 2 = 1 then D else 0,
   if x 2 = 2 then D else 0)

private abbrev CyclotomicIntegers := QuadraticAlgebra ℤ (-1 : ℤ) (-1 : ℤ)

private def cyclotomicRoot : CyclotomicIntegers := ⟨0, 1⟩

private def exactPhase (a : ZMod 3) : CyclotomicIntegers :=
  cyclotomicRoot ^ a.val

private def exactWeyl (v : WeylLabel) : Mat3 CyclotomicIntegers :=
  fun i j =>
    let j' : ZMod 3 := j
    if (i : ZMod 3) = j' + v.1 then exactPhase (-v.1 * v.2 + v.2 * j') else 0

private def exactHomogeneous (x : Charge) : FirstTits CyclotomicIntegers :=
  let D := exactWeyl (x 0, x 1)
  (if x 2 = 0 then D else 0,
   if x 2 = 1 then D else 0,
   if x 2 = 2 then D else 0)

private def exactCoefficientDouble (x y : Charge) : CyclotomicIntegers :=
  letI : Decidable (dependentGrades x y) := inferInstanceAs
    (Decidable (x = 0 ∨ y = 0 ∨ x = y ∨ x = -y))
  if dependentGrades x y then 2 else -exactPhase (gradeExponent x y)

private def ExactHomogeneousProduct (x y : Charge) : Prop :=
  firstTitsSquare (exactHomogeneous x + exactHomogeneous y) -
    firstTitsSquare (exactHomogeneous x) - firstTitsSquare (exactHomogeneous y) =
    exactCoefficientDouble x y • exactHomogeneous (x + y)

private instance (x y : Charge) : Decidable (ExactHomogeneousProduct x y) :=
  inferInstanceAs (Decidable (_ = _))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
/-- Split the kernel calculation into one row of nine Weyl labels at a time. -/
private theorem exactHomogeneous_product_rows
    (k l a b : ZMod 3) : ∀ w : WeylLabel,
    ExactHomogeneousProduct (chargeFrom (a,b) k) (chargeFrom w l) := by
  fin_cases k <;> fin_cases l <;> fin_cases a <;> fin_cases b <;> decide +kernel

private theorem exactHomogeneous_product_double (x y : Charge) :
    ExactHomogeneousProduct x y := by
  rw [← chargeFrom_components x, ← chargeFrom_components y]
  exact exactHomogeneous_product_rows (x 2) (y 2) (x 0) (x 1) (y 0,y 1)

private def evaluateCyclotomic : CyclotomicIntegers →ₐ[ℤ] ℂ :=
  QuadraticAlgebra.lift ⟨chargeRoot, by
    simp only [neg_smul, one_smul]
    linear_combination chargeRoot_quadratic⟩

@[simp] private theorem evaluateCyclotomic_omega :
    evaluateCyclotomic cyclotomicRoot = chargeRoot := by
  simp [evaluateCyclotomic, cyclotomicRoot]

private def mapTriple {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : FirstTits R) : FirstTits S :=
  (x.1.map f, x.2.1.map f, x.2.2.map f)

private theorem mapTriple_add {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x y : FirstTits R) : mapTriple f (x + y) = mapTriple f x + mapTriple f y := by
  rcases x with ⟨A,B,C⟩
  rcases y with ⟨A',B',C'⟩
  simp [mapTriple, Matrix.map_add, map_add]

private theorem mapTriple_sub {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x y : FirstTits R) : mapTriple f (x - y) = mapTriple f x - mapTriple f y := by
  rcases x with ⟨A,B,C⟩
  rcases y with ⟨A',B',C'⟩
  simp [mapTriple, Matrix.map_sub, map_sub]

private theorem mapTriple_smul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) (x : FirstTits R) : mapTriple f (r • x) = f r • mapTriple f x := by
  rcases x with ⟨A,B,C⟩
  simp [mapTriple, Matrix.map_smul', map_mul]

private theorem map_trace3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Mat3 R) : f (trace3 A) = trace3 (A.map f) := by
  simp [trace3]

private theorem map_adjugate3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Mat3 R) : (adjugate3 A).map f = adjugate3 (A.map f) := by
  ext i j
  change f (adjugate3 A i j) = _
  fin_cases i <;> fin_cases j <;> simp [adjugate3]

private theorem mapTriple_square {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : FirstTits R) : mapTriple f (firstTitsSquare x) = firstTitsSquare (mapTriple f x) := by
  rcases x with ⟨A,B,C⟩
  simp [mapTriple, firstTitsSquare, Matrix.map_add, Matrix.map_sub, Matrix.map_smul',
    Matrix.map_one, Matrix.map_mul, map_add, map_sub, map_mul, map_trace3, map_adjugate3]

private theorem evaluate_exactWeyl (v : WeylLabel) :
    (exactWeyl v).map evaluateCyclotomic.toRingHom = (weylMatrix v : Mat3 ℂ) := by
  ext i j
  let i' : ZMod 3 := i
  let j' : ZMod 3 := j
  change evaluateCyclotomic (if i' = j' + v.1 then exactPhase (-v.1*v.2+v.2*j') else 0) =
    if i' = j' + v.1 then chargePhase (-v.1*v.2+v.2*j') else 0
  split_ifs <;> simp [exactPhase, chargePhase]

private theorem evaluate_exactHomogeneous (x : Charge) :
    mapTriple evaluateCyclotomic.toRingHom (exactHomogeneous x) = homogeneousTits x := by
  simp only [mapTriple, exactHomogeneous, homogeneousTits]
  apply Prod.ext
  · by_cases h : x 2 = 0
    · simpa only [h, ↓reduceIte] using evaluate_exactWeyl (x 0, x 1)
    · simp [h, Matrix.map_zero]
  · apply Prod.ext
    · by_cases h : x 2 = 1
      · simpa only [h, ↓reduceIte] using evaluate_exactWeyl (x 0, x 1)
      · simp [h, Matrix.map_zero]
    · by_cases h : x 2 = 2
      · simpa only [h, ↓reduceIte] using evaluate_exactWeyl (x 0, x 1)
      · simp [h, Matrix.map_zero]

private theorem evaluate_exactCoefficientDouble (x y : Charge) :
    evaluateCyclotomic (exactCoefficientDouble x y) = 2 * gradedProductCoefficient x y := by
  by_cases h : dependentGrades x y
  · simpa [exactCoefficientDouble, gradedProductCoefficient, h] using
      (map_natCast evaluateCyclotomic 2)
  · simp [exactCoefficientDouble, gradedProductCoefficient, h, exactPhase]
    ring

/-- The homogeneous complex Weyl vectors multiply by the marked signed grade rule. -/
theorem homogeneousTits_product (x y : Charge) :
    polarProduct firstTitsSquare (homogeneousTits x) (homogeneousTits y) =
      gradedProductCoefficient x y • homogeneousTits (x + y) := by
  have h₀ := exactHomogeneous_product_double x y
  unfold ExactHomogeneousProduct at h₀
  have h := congrArg (mapTriple evaluateCyclotomic.toRingHom) h₀
  simp only [mapTriple_sub, mapTriple_square, mapTriple_add, mapTriple_smul,
    evaluate_exactHomogeneous] at h
  have he : evaluateCyclotomic.toRingHom (exactCoefficientDouble x y) =
      2 * gradedProductCoefficient x y := evaluate_exactCoefficientDouble x y
  rw [he] at h
  rw [polarProduct, h, smul_smul, ← mul_assoc, invOf_mul_self, one_mul]

end

end ThirteenPlanes
