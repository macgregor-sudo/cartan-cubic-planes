module

public import Mathlib.Analysis.Quaternion
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Native quaternionic qutrit objects

Native objects for the source mathematics:
`original/quaternionic_mub_bound.tex`, Definitions and results, equation (1).
The scalar field of the geometry is real; the entries and column inner product
are the literal, noncommutative quaternions. No diagonalization or bound is a
field of any definition. Matrix multiplication keeps its ordinary order.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

abbrev Outcome := Fin 3
abbrev Q := Quaternion ℝ
abbrev QVec := Outcome → Q
abbrev QMat := Matrix Outcome Outcome Q

/-- Quaternion conjugation fixes real scalars. Mathlib provides the operation
identity, which we package as its standard scalar-star compatibility instance. -/
instance realQuaternionStarModule : StarModule ℝ Q where
  star_smul r q := by simpa only [star_trivial] using Quaternion.star_smul r q

/-- Right quaternionic column inner product, conjugate linear in the first input. -/
def qInner (u v : QVec) : Q :=
  ∑ i, star (u i) * v i

/-- The actual rank-one matrix `u uᴴ`; it is a projector when `u` is unit. -/
def projector (u : QVec) : QMat :=
  fun i j => u i * star (u j)

/-- An ordered quaternionic orthonormal basis, stored as its column matrix.
Both ordinary unitarity equations are explicit. Equivalence with the usual
column Gram condition is a theorem obligation, not additional basis data. -/
structure QBasis where
  mat : QMat
  adjoint_mul : matᴴ * mat = 1
  mul_adjoint : mat * matᴴ = 1

namespace QBasis

def column (U : QBasis) (a : Outcome) : QVec := fun i => U.mat i a

def point (U : QBasis) (a : Outcome) : QMat := projector (U.column a)

/-- All nine ordinary squared-overlap equations, with no normal-form premise. -/
def MutuallyUnbiased (U V : QBasis) : Prop :=
  ∀ a b, Quaternion.normSq (qInner (U.column a) (V.column b)) = (1 / 3 : ℝ)

/-- The coordinate basis supplies a basic nonvacuity witness for the carrier. -/
def coordinate : QBasis where
  mat := 1
  adjoint_mul := by simp
  mul_adjoint := by simp

end QBasis

/-- Real quaternionic matrix trace, on all matrices. Quaternion-valued trace is
not used: its usual cyclicity theorem would be false here. -/
def rtrace (A : QMat) : ℝ := ∑ i, (A i i).re

/-- The source half Jordan product, using central real scalar multiplication. -/
def jordan (A B : QMat) : QMat := (1 / 2 : ℝ) • (A * B + B * A)

/-- The source trace pairing. Positivity on Hermitian matrices remains to prove. -/
def traceForm (A B : QMat) : ℝ := rtrace (jordan A B)

/-- The literal real Frobenius square, defined for arbitrary matrices. -/
def frobeniusSq (A : QMat) : ℝ := ∑ i, ∑ j, Quaternion.normSq (A i j)

/-- The real linear subspace of actual Hermitian quaternionic matrices. -/
def hermitianSubmodule : Submodule ℝ QMat where
  carrier := {A | A.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' := fun hA hB => hA.add hB
  smul_mem' := by
    intro r A hA
    change (r • A)ᴴ = r • A
    simp only [Matrix.conjTranspose_smul, star_trivial, hA.eq]

/-- The trace map is real linear; this does not assert cyclicity. -/
def rtraceLinear : QMat →ₗ[ℝ] ℝ where
  toFun := rtrace
  map_add' A B := by simp [rtrace, Finset.sum_add_distrib]
  map_smul' r A := by simp [rtrace, Finset.mul_sum]

abbrev Herm3 := hermitianSubmodule

/-- The native traceless Hermitian real subspace. Its dimension is an obligation. -/
def tracelessHermitianSubmodule : Submodule ℝ QMat :=
  hermitianSubmodule ⊓ rtraceLinear.ker

abbrev J0 := tracelessHermitianSubmodule

/-- A positive quaternionic Jordan frame: only the ordinary source axioms.
No columns, diagonalizer, frame plane dimension, or completion is supplied. -/
structure Frame where
  point : Outcome → QMat
  hermitian : ∀ a, (point a).IsHermitian
  trace_one : ∀ a, rtrace (point a) = 1
  idempotent : ∀ a, jordan (point a) (point a) = point a
  orthogonal : ∀ a b, a ≠ b → jordan (point a) (point b) = 0
  sum_points : ∑ a, point a = 1

namespace Frame

/-- The ordinary trace-overlap definition; the basis dictionary must identify it
with squared quaternionic column overlaps. -/
def MutuallyUnbiased (F G : Frame) : Prop :=
  ∀ a b, traceForm (F.point a) (G.point b) = (1 / 3 : ℝ)

end Frame

/-- All 27 entries of the exact centered source tensor. -/
def centeredTensor (F G H : Outcome → QMat) (a b c : Outcome) : ℝ :=
  traceForm (jordan (F a) (G b)) (H c) - (1 / 9 : ℝ)

/-- The squared centered tensor, with no replacement scalar or certificate. -/
def w (F G H : Outcome → QMat) : ℝ :=
  ∑ a, ∑ b, ∑ c, (centeredTensor F G H a b c) ^ 2

/-- The source rescaling of the literal weight. -/
def s (F G H : Outcome → QMat) : ℝ := 6 * w F G H

def basisW (U V W : QBasis) : ℝ := w U.point V.point W.point

def basisS (U V W : QBasis) : ℝ := s U.point V.point W.point

def frameW (F G H : Frame) : ℝ := w F.point G.point H.point

def frameS (F G H : Frame) : ℝ := s F.point G.point H.point

/-- Distinct indices must have mutually unbiased bases; no finiteness or
cardinality restriction is imposed by this predicate. -/
def IsMUBFamily {ι : Type*} (B : ι → QBasis) : Prop :=
  Pairwise (fun i j => (B i).MutuallyUnbiased (B j))

def IsMUBFrameFamily {ι : Type*} (F : ι → Frame) : Prop :=
  Pairwise (fun i j => (F i).MutuallyUnbiased (F j))

/-- Real diagonal matrices in the literal quaternionic matrix carrier. -/
def realDiagonal (d : Outcome → ℝ) : QMat :=
  Matrix.diagonal (fun i => (d i : Q))

end QuaternionicMUB
