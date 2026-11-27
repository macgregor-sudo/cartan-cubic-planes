/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Trace

@[expose] public section
noncomputable section
open scoped BigOperators InnerProductSpace

namespace Challenge

/-- The bilinear product obtained by raising one index of a real symmetric cubic tensor. -/
structure Cubic (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  mul : V →ₗ[ℝ] V →ₗ[ℝ] V
  comm : ∀ x y, mul x y = mul y x
  symm : ∀ x y z, ⟪mul x y, z⟫_ℝ = ⟪mul x z, y⟫_ℝ

section Cubics
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def Cubic.eval (d : Cubic V) (x : V) : ℝ := ⟪d.mul x x, x⟫_ℝ
def Eikonal (d : Cubic V) (c : ℝ) : Prop :=
  0 < c ∧ ∀ x, ‖d.mul x x‖ ^ 2 = c * ‖x‖ ^ 4
def Closed (d : Cubic V) (U : Submodule ℝ V) : Prop :=
  ∀ ⦃x y⦄, x ∈ U → y ∈ U → d.mul x y ∈ U
def OrthogonalDecomposition {ι : Type*} (U : ι → Submodule ℝ V) : Prop :=
  Pairwise (fun i j => (U i).IsOrtho (U j)) ∧ (⨆ i, U i) = ⊤
def Planes {ι : Type*} (d : Cubic V) (U : ι → Submodule ℝ V) : Prop :=
  OrthogonalDecomposition U ∧ ∀ i, Module.finrank ℝ (U i) = 2 ∧ Closed d (U i)
def Harmonic (d : Cubic V) : Prop := ∀ x, LinearMap.trace ℝ V (d.mul x) = 0

def mixedSpace (d : Cubic V) (U W : Submodule ℝ V) : Submodule ℝ V :=
  Submodule.map₂ d.mul U W

variable [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]

/-- One half of the overlap trace of the plane and mixed-product projections. -/
def share (d : Cubic V) (U : ι → Submodule ℝ V) (i j k : ι) : ℝ :=
  (1 / 2) * LinearMap.trace ℝ V
    ((U k).starProjection.toLinearMap.comp (mixedSpace d (U i) (U j)).starProjection.toLinearMap)
def pencilSquare (d : Cubic V) (U : ι → Submodule ℝ V) (t : ℝ) (x : V) : V :=
  let D := ∑ i, (U i).starProjection (d.mul ((U i).starProjection x) ((U i).starProjection x))
  D + t • (d.mul x x - D)
def pencil (d : Cubic V) (U : ι → Submodule ℝ V) (t : ℝ) (x : V) : ℝ :=
  ⟪pencilSquare d U t x, x⟫_ℝ
def pencilEnergy (d : Cubic V) (U : ι → Submodule ℝ V) (c t : ℝ) (x : V) : ℝ :=
  ‖pencilSquare d U t x‖ ^ 2 / c

end Cubics
abbrev FieldSpace (m : ℕ) := EuclideanSpace ℂ (Fin m)
abbrev IncreasingTriple (m : ℕ) := {t : Fin m × Fin m × Fin m // t.1 < t.2.1 ∧ t.2.1 < t.2.2}
abbrev RealTrilinear := ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ
def fieldPolynomial {m : ℕ} (T : IncreasingTriple m → RealTrilinear) (z : FieldSpace m) : ℝ :=
  (∑ i, (z i ^ 3).re) + ∑ t, T t (z t.1.1) (z t.1.2.1) (z t.1.2.2)
def RadialFieldEnergy {m : ℕ} (T : IncreasingTriple m → RealTrilinear) : Prop :=
  ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
    ‖gradient (fieldPolynomial T) x‖ ^ 2 = ‖gradient (fieldPolynomial T) y‖ ^ 2
abbrev ComplexMatrix3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev ComplexHermitian3 := selfAdjoint.submodule ℝ ComplexMatrix3
def TracelessComplexHermitian3 : Submodule ℝ ComplexHermitian3 :=
  ((Matrix.traceLinearMap (Fin 3) ℝ ℂ).comp ComplexHermitian3.subtype).ker
def complexMatrix (x : TracelessComplexHermitian3) : ComplexMatrix3 := x.val.val

/- Cayley–Dickson convention and upper-entry coordinates from the Apache-2.0
   Challenge accompanying “On sequential ideal measurements in the exceptional Jordan algebra”. -/
abbrev Octonion := Quaternion ℝ × Quaternion ℝ
def octMul (x y : Octonion) : Octonion :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)
def octConj (x : Octonion) : Octonion := (star x.1, -x.2)
def octScalar (r : ℝ) : Octonion := ((r : Quaternion ℝ), 0)

/-- Real diagonal and upper entries in positions 01, 02, and 12 of an octonionic Hermitian matrix. -/
abbrev Hermitian3 := (Fin 3 → ℝ) × (Fin 3 → Octonion)
def hermitianMatrix (x : Hermitian3) : Matrix (Fin 3) (Fin 3) Octonion :=
  ![![octScalar (x.1 0), x.2 0, x.2 1],
    ![octConj (x.2 0), octScalar (x.1 1), x.2 2],
    ![octConj (x.2 1), octConj (x.2 2), octScalar (x.1 2)]]
def octMatrixMul (x y : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  fun i j => ∑ k, octMul (x i k) (y k j)
def jordanMul (x y : Hermitian3) : Hermitian3 :=
  let A := hermitianMatrix x
  let B := hermitianMatrix y
  let M := (1 / 2 : ℝ) • (octMatrixMul A B + octMatrixMul B A)
  (fun i => (M i i).1.re, ![M 0 1, M 0 2, M 1 2])
def hermitianOne : Hermitian3 := (fun _ => 1, fun _ => 0)
def jordanTrace (x : Hermitian3) : ℝ := ∑ i, x.1 i
def jordanTraceLinear : Hermitian3 →ₗ[ℝ] ℝ where
  toFun := jordanTrace
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' r x := by simp [jordanTrace, Finset.mul_sum]
def TracelessHermitian3 : Submodule ℝ Hermitian3 := jordanTraceLinear.ker

section CartanForms
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A complex Hermitian trace cube, transported by an isometry for the trace metric. -/
def ComplexCartanForm (W : V → ℝ) (scale : ℝ) : Prop :=
  ∃ I : V ≃ₗ[ℝ] TracelessComplexHermitian3,
    (∀ x y, ⟪x, y⟫_ℝ = (Matrix.trace (complexMatrix (I x) * complexMatrix (I y))).re) ∧
    ∀ x, W x = scale * (Matrix.trace (complexMatrix (I x) ^ 3)).re

/-- An octonionic Hermitian trace cube, transported by an isometry for the trace metric. -/
def AlbertCartanForm (W : V → ℝ) (scale : ℝ) : Prop :=
  ∃ I : V ≃ₗ[ℝ] TracelessHermitian3,
    (∀ x y, ⟪x, y⟫_ℝ = jordanTrace (jordanMul (I x) (I y))) ∧
    ∀ x, W x = scale * jordanTrace (jordanMul (jordanMul (I x) (I x)) (I x))

variable {ι : Type*} [Fintype ι]
def ProperClosedDecomposition (d : Cubic V) (U : ι → Submodule ℝ V) : Prop :=
  OrthogonalDecomposition U ∧ (∀ i, U i ≠ ⊥ ∧ Closed d (U i)) ∧ 1 < Fintype.card ι
def BlocksOfDimension (U : ι → Submodule ℝ V) (k n : ℕ) : Prop :=
  Fintype.card ι = k ∧ ∀ i, Module.finrank ℝ (U i) = n
def OctetAndNine (d : Cubic V) (U : ι → Submodule ℝ V) (c : ℝ) : Prop :=
  Fintype.card ι = 10 ∧ ∃ i, Module.finrank ℝ (U i) = 8 ∧
    (∀ j, j ≠ i → Module.finrank ℝ (U j) = 2) ∧
    ComplexCartanForm (fun x : U i => d.eval x) (Real.sqrt (6 * c))

end CartanForms

/-- An ordered list of the three trace-one orthogonal idempotents of an Albert frame. -/
structure AlbertFrame (p : Fin 3 → Hermitian3) : Prop where
  trace_one : ∀ a, jordanTrace (p a) = 1
  idempotent : ∀ a, jordanMul (p a) (p a) = p a
  orthogonal : ∀ a b, a ≠ b → jordanMul (p a) (p b) = 0
  sum_unit : ∑ a, p a = hermitianOne

/-- Two Albert frames are unbiased when all nine pairwise trace overlaps are one third. -/
def AlbertUnbiased (p q : Fin 3 → Hermitian3) : Prop :=
  ∀ a b, jordanTrace (jordanMul (p a) (q b)) = 1 / 3

/-- A real two-plane in the Albert trace kernel closed under the traceless Jordan product. -/
def ClosedAlbertPlane (P : Submodule ℝ TracelessHermitian3) : Prop :=
  Module.finrank ℝ P = 2 ∧ ∀ x ∈ P, ∀ y ∈ P, ∃ z ∈ P,
    (z : Hermitian3) = jordanMul x y - (jordanTrace (jordanMul x y) / 3) • hermitianOne

/-- Orthogonality of traceless Albert subspaces for the Jordan trace form. -/
def AlbertPlaneOrthogonal (P Q : Submodule ℝ TracelessHermitian3) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, jordanTrace (jordanMul x y) = 0

/-- The share of a triple of planes from pairwise unbiased Albert frames, in trace coordinates. -/
def albertFrameShare (p q r : Fin 3 → Hermitian3) : ℝ :=
  6 * ∑ a, ∑ b, ∑ d, (jordanTrace (jordanMul (jordanMul (p a) (q b)) (r d)) - 1 / 9) ^ 2

/-- A thirteen-plane system whose planes have exactly 52 positive shares. -/
noncomputable def SparseAlbertSystem (F : Fin 13 → Fin 3 → Hermitian3) : Prop := by
  classical
  exact (∀ i, AlbertFrame (F i)) ∧ Pairwise (fun i j => AlbertUnbiased (F i) (F j)) ∧
    (Finset.univ.filter fun t : IncreasingTriple 13 =>
      0 < albertFrameShare (F t.val.1) (F t.val.2.1) (F t.val.2.2)).card = 52

end Challenge
namespace Challenge.Quaternionic
open scoped Matrix
abbrev Outcome := Fin 3
abbrev Q := Quaternion ℝ
abbrev QMat := Matrix Outcome Outcome Q
abbrev Basis := ↥(unitary QMat)
def unbiased (U V : Basis) : Prop :=
  ∀ a b, Quaternion.normSq (∑ i, star (U.val i a) * V.val i b) = (1 / 3 : ℝ)
def unbiasedTriple (U V W : Basis) : Prop := unbiased U V ∧ unbiased U W ∧ unbiased V W
def point (U : Basis) (a : Outcome) : QMat := fun i j => U.val i a * star (U.val j a)
def jordan (A B : QMat) : QMat := (1 / 2 : ℝ) • (A * B + B * A)
def tracePairing (A B : QMat) : ℝ := ∑ i, (jordan A B i i).re
def share (U V W : Basis) : ℝ := 6 * ∑ a, ∑ b, ∑ c,
  (tracePairing (jordan (point U a) (point V b)) (point W c) - (1 / 9 : ℝ)) ^ 2
def ω : Q := ⟨-1 / 2, Real.sqrt 3 / 2, 0, 0⟩
def j : Q := ⟨0, 0, 1, 0⟩
def fourier : QMat := fun a b => (1 / Real.sqrt 3) • ω ^ (a.val * b.val)
def unitPhases (p : Outcome → Q) : Prop := ∀ i, Quaternion.normSq (p i) = 1
def normalForm (U V W : Basis) (p : Outcome → Q) : Prop :=
  ∃ (L : Basis) (σ τ υ : Equiv.Perm Outcome) (u v w : Outcome → Q),
    unitPhases u ∧ unitPhases v ∧ unitPhases w ∧
    L.val * U.val.submatrix id σ * Matrix.diagonal u = 1 ∧
    L.val * V.val.submatrix id τ * Matrix.diagonal v = fourier ∧
    L.val * W.val.submatrix id υ * Matrix.diagonal w = Matrix.diagonal p * fourier
def attainingPhases : Outcome → Q :=
  let r := Real.sqrt (Real.sqrt 3)
  let A : ℝ := (r + (r ^ 2 - 1) / Real.sqrt 2) / 2
  let C : ℝ := (r - (r ^ 2 - 1) / Real.sqrt 2) / 2
  ![(A : Q) + C • j, ω ^ 2 * ((1 / Real.sqrt 2 : ℝ) • (1 - j)), -(ω * ((C : Q) + A • j))]
def balance (q : Q) : ℝ := Complex.normSq ⟨q.re, q.imI⟩ - Complex.normSq ⟨q.imJ, q.imK⟩
def extremalBalance (x y z : ℝ) : Prop :=
  ∃ t : ℝ, t ^ 2 = 2 * Real.sqrt 3 - 3 ∧
    ((x = 0 ∧ y = t ∧ z = -t) ∨ (x = t ∧ y = 0 ∧ z = -t) ∨ (x = t ∧ y = -t ∧ z = 0))

end Challenge.Quaternionic
