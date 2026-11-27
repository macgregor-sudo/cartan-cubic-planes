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
/-- The diagonal value of the symmetric trilinear form, obtained by pairing the square with the vector. -/
def Cubic.eval (d : Cubic V) (x : V) : ℝ := ⟪d.mul x x, x⟫_ℝ
/-- The eikonal identity at positive strength `c`. The squared norm of the cubic
gradient is `9 * c` times the fourth power of the norm of the input. -/
def Eikonal (d : Cubic V) (c : ℝ) : Prop :=
  0 < c ∧ ∀ x, ‖d.mul x x‖ ^ 2 = c * ‖x‖ ^ 4
/-- A subspace closed under the cubic's bilinear product. -/
def Closed (d : Cubic V) (U : Submodule ℝ V) : Prop :=
  ∀ ⦃x y⦄, x ∈ U → y ∈ U → d.mul x y ∈ U
/-- Pairwise orthogonal subspaces whose span is the whole space. -/
def OrthogonalDecomposition {ι : Type*} (U : ι → Submodule ℝ V) : Prop :=
  Pairwise (fun i j => (U i).IsOrtho (U j)) ∧ (⨆ i, U i) = ⊤
/-- A complete orthogonal decomposition into two-dimensional subspaces closed under the cubic product. -/
def Planes {ι : Type*} (d : Cubic V) (U : ι → Submodule ℝ V) : Prop :=
  OrthogonalDecomposition U ∧ ∀ i, Module.finrank ℝ (U i) = 2 ∧ Closed d (U i)
/-- In finite dimensions, harmonicity of the cubic polynomial is equivalent to
zero trace for the multiplication operator associated with each vector. -/
def Harmonic (d : Cubic V) : Prop := ∀ x, LinearMap.trace ℝ V (d.mul x) = 0

/-- The real span of products with one factor in each of the indicated subspaces. -/
def mixedSpace (d : Cubic V) (U W : Submodule ℝ V) : Submodule ℝ V :=
  Submodule.map₂ d.mul U W

variable [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]

/-- Half the trace of the composition of the orthogonal projector onto `U k` with
the orthogonal projector onto the mixed product space of `U i` and `U j`. -/
def share (d : Cubic V) (U : ι → Submodule ℝ V) (i j k : ι) : ℝ :=
  (1 / 2) * LinearMap.trace ℝ V
    ((U k).starProjection.toLinearMap.comp (mixedSpace d (U i) (U j)).starProjection.toLinearMap)
/-- The pencil's square map. It retains the sum of the projected squares on the
individual subspaces and multiplies the remaining part of the cubic's square map by `t`. -/
def pencilSquare (d : Cubic V) (U : ι → Submodule ℝ V) (t : ℝ) (x : V) : V :=
  let D := ∑ i, (U i).starProjection (d.mul ((U i).starProjection x) ((U i).starProjection x))
  D + t • (d.mul x x - D)
/-- The cubic evaluated by pairing the pencil's square map with the input vector. -/
def pencil (d : Cubic V) (U : ι → Submodule ℝ V) (t : ℝ) (x : V) : ℝ :=
  ⟪pencilSquare d U t x, x⟫_ℝ
/-- For positive strength `c`, the squared gradient norm of the pencil divided by
`9 * c`, or equivalently the squared norm of the pencil's square map divided by `c`. -/
def pencilEnergy (d : Cubic V) (U : ι → Submodule ℝ V) (c t : ℝ) (x : V) : ℝ :=
  ‖pencilSquare d U t x‖ ^ 2 / c

end Cubics
/-- The Euclidean space of `m` complex coordinates, with its real inner product for gradients. -/
abbrev FieldSpace (m : ℕ) := EuclideanSpace ℂ (Fin m)
/-- Three distinct field or plane indices in increasing order, one representative per unordered triple. -/
abbrev IncreasingTriple (m : ℕ) := {t : Fin m × Fin m × Fin m // t.1 < t.2.1 ∧ t.2.1 < t.2.2}
/-- A real-valued form on three complex coordinates, real-linear in each argument. -/
abbrev RealTrilinear := ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ
/-- The sum of the real parts of the diagonal cubes and one real trilinear
term on each unordered triple of distinct coordinates. -/
def fieldPolynomial {m : ℕ} (T : IncreasingTriple m → RealTrilinear) (z : FieldSpace m) : ℝ :=
  (∑ i, (z i ^ 3).re) + ∑ t, T t (z t.1.1) (z t.1.2.1) (z t.1.2.2)
/-- The squared norm of the field polynomial's gradient depends only on the input norm. -/
def RadialFieldEnergy {m : ℕ} (T : IncreasingTriple m → RealTrilinear) : Prop :=
  ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
    ‖gradient (fieldPolynomial T) x‖ ^ 2 = ‖gradient (fieldPolynomial T) y‖ ^ 2
/-- Complex matrices of size three. -/
abbrev ComplexMatrix3 := Matrix (Fin 3) (Fin 3) ℂ
/-- The real subspace of Hermitian matrices of size three over the complexes. -/
abbrev ComplexHermitian3 := selfAdjoint.submodule ℝ ComplexMatrix3
/-- The kernel of the matrix trace on the real space of complex Hermitian matrices. -/
def TracelessComplexHermitian3 : Submodule ℝ ComplexHermitian3 :=
  ((Matrix.traceLinearMap (Fin 3) ℝ ℂ).comp ComplexHermitian3.subtype).ker
/-- The matrix underlying a traceless complex Hermitian element. -/
def complexMatrix (x : TracelessComplexHermitian3) : ComplexMatrix3 := x.val.val

/-- Octonions as pairs of real quaternions. The Cayley–Dickson convention and
Hermitian upper-entry coordinates follow the Apache-2.0 Challenge accompanying
“On sequential ideal measurements in the exceptional Jordan algebra”. -/
abbrev Octonion := Quaternion ℝ × Quaternion ℝ
/-- The Cayley–Dickson product \((a,b)(c,d)=(ac-\bar d b, da+b\bar c)\). -/
def octMul (x y : Octonion) : Octonion :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)
/-- Octonion conjugation, which conjugates the first quaternion and negates the second. -/
def octConj (x : Octonion) : Octonion := (star x.1, -x.2)
/-- The real scalar embedded in the first quaternion of an octonion. -/
def octScalar (r : ℝ) : Octonion := ((r : Quaternion ℝ), 0)

/-- Real diagonal and upper entries in positions 01, 02, and 12 of an octonionic Hermitian matrix. -/
abbrev Hermitian3 := (Fin 3 → ℝ) × (Fin 3 → Octonion)
/-- The Hermitian matrix reconstructed from its real diagonal and upper entries. -/
def hermitianMatrix (x : Hermitian3) : Matrix (Fin 3) (Fin 3) Octonion :=
  ![![octScalar (x.1 0), x.2 0, x.2 1],
    ![octConj (x.2 0), octScalar (x.1 1), x.2 2],
    ![octConj (x.2 1), octConj (x.2 2), octScalar (x.1 2)]]
/-- The binary row-by-column matrix product with the indicated order of octonion factors. -/
def octMatrixMul (x y : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  fun i j => ∑ k, octMul (x i k) (y k j)
/-- The Hermitian Jordan product, given by half the sum of the two matrix products in opposite orders. -/
def jordanMul (x y : Hermitian3) : Hermitian3 :=
  let A := hermitianMatrix x
  let B := hermitianMatrix y
  let M := (1 / 2 : ℝ) • (octMatrixMul A B + octMatrixMul B A)
  (fun i => (M i i).1.re, ![M 0 1, M 0 2, M 1 2])
/-- The identity matrix in Hermitian coordinates. -/
def hermitianOne : Hermitian3 := (fun _ => 1, fun _ => 0)
/-- The sum of the three real diagonal entries. -/
def jordanTrace (x : Hermitian3) : ℝ := ∑ i, x.1 i
/-- The Jordan trace as a real linear map. -/
def jordanTraceLinear : Hermitian3 →ₗ[ℝ] ℝ where
  toFun := jordanTrace
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' r x := by simp [jordanTrace, Finset.mul_sum]
/-- The real trace-zero subspace of the octonionic Hermitian Jordan algebra. -/
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
/-- A complete orthogonal decomposition into at least two nonzero subspaces closed under the cubic product. -/
def ProperClosedDecomposition (d : Cubic V) (U : ι → Submodule ℝ V) : Prop :=
  OrthogonalDecomposition U ∧ (∀ i, U i ≠ ⊥ ∧ Closed d (U i)) ∧ 1 < Fintype.card ι
/-- Exactly `k` blocks, each of real dimension `n`. -/
def BlocksOfDimension (U : ι → Submodule ℝ V) (k n : ℕ) : Prop :=
  Fintype.card ι = k ∧ ∀ i, Module.finrank ℝ (U i) = n
/-- Nine two-dimensional blocks and one eight-dimensional block carrying the
complex Hermitian trace cubic at scale `Real.sqrt (6 * c)`. -/
def OctetAndNine (d : Cubic V) (U : ι → Submodule ℝ V) (c : ℝ) : Prop :=
  Fintype.card ι = 10 ∧ ∃ i, Module.finrank ℝ (U i) = 8 ∧
    (∀ j, j ≠ i → Module.finrank ℝ (U j) = 2) ∧
    ComplexCartanForm (fun x : U i => d.eval x) (Real.sqrt (6 * c))

end CartanForms

/-- Theorem A(i). The field count and the two proper Cartan models. -/
theorem fields_classification {m : ℕ} (hm : 1 ≤ m) (T : IncreasingTriple m → RealTrilinear)
    (hT : RadialFieldEnergy T) :
    m = 1 ∨ (m = 4 ∧ ComplexCartanForm (fieldPolynomial T) (Real.sqrt 6)) ∨
      (m = 13 ∧ AlbertCartanForm (fieldPolynomial T) (Real.sqrt 6)) := by sorry

/-- Radial field polynomials exist with four and with thirteen complex fields. -/
theorem fields_realizations :
    (∃ T : IncreasingTriple 4 → RealTrilinear, RadialFieldEnergy T) ∧
      (∃ T : IncreasingTriple 13 → RealTrilinear, RadialFieldEnergy T) := by sorry

section Decompositions
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Theorem A(ii). The four proper closed decomposition patterns. -/
theorem closed_decomposition_classification {ι : Type*} [Fintype ι]
    (d : Cubic V) (c : ℝ) (U : ι → Submodule ℝ V)
    (hd : Eikonal d c) (hU : ProperClosedDecomposition d U) :
    (Module.finrank ℝ V = 4 ∧ ¬ Harmonic d ∧ BlocksOfDimension U 4 1) ∨
    (Module.finrank ℝ V = 8 ∧ BlocksOfDimension U 4 2) ∨
    (Module.finrank ℝ V = 26 ∧ (BlocksOfDimension U 13 2 ∨ OctetAndNine d U c)) := by sorry

/-- Each of the four closed-decomposition patterns
has a realization by an eikonal cubic of strength one. The four-line example is nonharmonic. -/
theorem closed_decomposition_realizations :
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 4))) (U : Fin 4 → Submodule ℝ (EuclideanSpace ℝ (Fin 4))),
      Eikonal d 1 ∧ ¬ Harmonic d ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 4 1) ∧
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 8))) (U : Fin 4 → Submodule ℝ (EuclideanSpace ℝ (Fin 8))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 4 2) ∧
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 26))) (U : Fin 13 → Submodule ℝ (EuclideanSpace ℝ (Fin 26))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ BlocksOfDimension U 13 2) ∧
    (∃ (d : Cubic (EuclideanSpace ℝ (Fin 26))) (U : Fin 10 → Submodule ℝ (EuclideanSpace ℝ (Fin 26))),
      Eikonal d 1 ∧ ProperClosedDecomposition d U ∧ OctetAndNine d U 1) := by sorry

/-- Let at least three closed planes form an orthogonal decomposition for a
positive-strength eikonal cubic. On distinct indices the share lies in `[0,1]`.
It is one exactly when the third plane lies in the mixed product space of the first two,
and zero exactly when it is orthogonal to that space. The shares sum to two over
the remaining planes for each pair and to \(m(m-1)/3\) over unordered triples. -/
theorem sum_rule {m : ℕ} (hm : 3 ≤ m) (d : Cubic V) (c : ℝ) (U : Fin m → Submodule ℝ V)
    (hd : Eikonal d c) (hU : Planes d U) :
    (∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      share d U i j k ∈ Set.Icc 0 1 ∧
      (share d U i j k = 1 ↔ U k ≤ mixedSpace d (U i) (U j)) ∧
      (share d U i j k = 0 ↔ (U k).IsOrtho (mixedSpace d (U i) (U j)))) ∧
    (∀ i j, i ≠ j → (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), share d U i j k) = 2) ∧
    (∑ t : IncreasingTriple m, share d U t.1.1 t.1.2.1 t.1.2.2) = (m : ℝ) * ((m : ℝ) - 1) / 3 := by sorry

open Classical in
/-- At least 52 unordered triples have positive share in a complete orthogonal
decomposition into thirteen closed planes for a positive-strength eikonal cubic.
If exactly 52 shares are positive, every share is zero or one. -/
theorem thirteen_plane_share_support (d : Cubic V) (c : ℝ) (U : Fin 13 → Submodule ℝ V)
    (hd : Eikonal d c) (hU : Planes d U) :
    let support := Finset.univ.filter (fun t : IncreasingTriple 13 =>
      0 < share d U t.val.1 t.val.2.1 t.val.2.2)
    52 ≤ support.card ∧ (support.card = 52 → ∀ t : IncreasingTriple 13,
      share d U t.val.1 t.val.2.1 t.val.2.2 = 0 ∨
      share d U t.val.1 t.val.2.1 t.val.2.2 = 1) := by sorry

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- For two eikonal cubics of equal strength with a common labelled decomposition
into more than one closed plane, equality of energy on every
sum of three distinct planes forces equal parameters. Away from zero and one, the two
cubics and their pencils agree up to the same overall sign. -/
theorem energy_recovery_labeled (d e : Cubic V) (c t s : ℝ) (U : ι → Submodule ℝ V)
    (hd : Eikonal d c) (he : Eikonal e c) (hU : Planes d U) (hU' : Planes e U)
    (hm : 1 < Fintype.card ι)
    (h : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x ∈ (U i ⊔ U j) ⊔ U k,
      pencilEnergy d U c t x = pencilEnergy e U c s x) :
    t = s ∧ (t ≠ 0 → t ≠ 1 → ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ x, e.eval x = ε * d.eval x ∧ pencil e U s x = ε * pencil d U t x) := by sorry

/-- At either parameter zero or one, an eikonal cubic on a
complete system of more than one closed plane has a competitor of the same strength
and on the same system, with identical energy everywhere and a pencil different even up to sign. -/
theorem energy_recovery_endpoints (d : Cubic V) (c t : ℝ) (U : ι → Submodule ℝ V)
    (hd : Eikonal d c) (hU : Planes d U) (hm : 1 < Fintype.card ι) (ht : t = 0 ∨ t = 1) :
    ∃ e : Cubic V, Eikonal e c ∧ Planes e U ∧
      (∀ x, pencilEnergy e U c t x = pencilEnergy d U c t x) ∧
      pencil e U t ≠ pencil d U t ∧ pencil e U t ≠ fun x => -pencil d U t x := by sorry

/-- For two eikonal cubics of the same strength, each with a
complete system of more than one closed plane and a positive parameter other than one,
equal energies on the full space determine a bijection matching their planes and force equal parameters.
The resulting pencils agree up to an overall sign. -/
theorem energy_recovery_unlabelled (d e : Cubic V) (c t s : ℝ)
    (U : ι → Submodule ℝ V) (W : κ → Submodule ℝ V)
    (hd : Eikonal d c) (he : Eikonal e c) (hU : Planes d U) (hW : Planes e W)
    (hm : 1 < Fintype.card ι) (hn : 1 < Fintype.card κ)
    (ht : 0 < t) (hs : 0 < s) (ht' : t ≠ 1) (hs' : s ≠ 1)
    (h : ∀ x, pencilEnergy d U c t x = pencilEnergy e W c s x) :
    ∃ f : ι ≃ κ, (∀ i, U i = W (f i)) ∧ t = s ∧
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x, pencil e W s x = ε * pencil d U t x := by sorry

end Decompositions

/-- Three ordered trace-one Jordan idempotents with pairwise zero products and sum the unit. -/
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

/-- Six times the sum of squared Jordan triple traces of the frame idempotents
after centering each trace by `1/9`. On distinct triples of a pairwise unbiased
thirteen-frame system, the Solution identifies this formula with the plane projection share
in `albertFrameShare_eq_nativeProjection`. -/
def albertFrameShare (p q r : Fin 3 → Hermitian3) : ℝ :=
  6 * ∑ a, ∑ b, ∑ d, (jordanTrace (jordanMul (jordanMul (p a) (q b)) (r d)) - 1 / 9) ^ 2

/-- Thirteen pairwise unbiased Albert frames with exactly 52 positive frame shares on unordered triples. -/
noncomputable def SparseAlbertSystem (F : Fin 13 → Fin 3 → Hermitian3) : Prop := by
  classical
  exact (∀ i, AlbertFrame (F i)) ∧ Pairwise (fun i j => AlbertUnbiased (F i) (F j)) ∧
    (Finset.univ.filter fun t : IncreasingTriple 13 =>
      0 < albertFrameShare (F t.val.1) (F t.val.2.1) (F t.val.2.2)).card = 52

/-- Twelve pairwise unbiased Albert frames admit exactly one completing frame as an unordered set.
Twelve pairwise orthogonal closed Albert planes likewise admit exactly one completing closed plane. -/
theorem albertCompletion :
    (∀ F : Fin 12 → Fin 3 → Hermitian3, (∀ i, AlbertFrame (F i)) →
      Pairwise (fun i j => AlbertUnbiased (F i) (F j)) →
      ∃ q : Fin 3 → Hermitian3, AlbertFrame q ∧ (∀ i, AlbertUnbiased (F i) q) ∧
        ∀ q' : Fin 3 → Hermitian3, AlbertFrame q' → (∀ i, AlbertUnbiased (F i) q') →
          Set.range q' = Set.range q) ∧
    (∀ P : Fin 12 → Submodule ℝ TracelessHermitian3, (∀ i, ClosedAlbertPlane (P i)) →
      Pairwise (fun i j => AlbertPlaneOrthogonal (P i) (P j)) →
      ∃! Q : Submodule ℝ TracelessHermitian3,
        ClosedAlbertPlane Q ∧ ∀ i, AlbertPlaneOrthogonal (P i) Q) := by
  sorry

/-- A pairwise unbiased thirteen-frame Albert system with 52 positive shares exists.
Any two such systems are related by a unital Jordan automorphism after a permutation of
the frames and a separate permutation of the three idempotents in each frame. -/
theorem albertSparsestSystem :
    (∃ F : Fin 13 → Fin 3 → Hermitian3, SparseAlbertSystem F) ∧
    (∀ F G : Fin 13 → Fin 3 → Hermitian3, SparseAlbertSystem F → SparseAlbertSystem G →
      ∃ (φ : Hermitian3 ≃ₗ[ℝ] Hermitian3) (σ : Equiv.Perm (Fin 13))
        (τ : Fin 13 → Equiv.Perm (Fin 3)),
        φ hermitianOne = hermitianOne ∧
        (∀ x y, φ (jordanMul x y) = jordanMul (φ x) (φ y)) ∧
        ∀ i a, φ (F i a) = G (σ i) (τ i a)) := by sorry

end Challenge
namespace Challenge.Quaternionic
open scoped Matrix
/-- The three column indices of a quaternionic basis. -/
abbrev Outcome := Fin 3
/-- Real quaternions. -/
abbrev Q := Quaternion ℝ
/-- Three-by-three matrices over the quaternions. -/
abbrev QMat := Matrix Outcome Outcome Q
/-- An ordered orthonormal quaternionic basis, given by the columns of a unitary matrix. -/
abbrev Basis := ↥(unitary QMat)
/-- Two quaternionic bases are unbiased when every cross-basis inner product has squared norm `1/3`. -/
def unbiased (U V : Basis) : Prop :=
  ∀ a b, Quaternion.normSq (∑ i, star (U.val i a) * V.val i b) = (1 / 3 : ℝ)
/-- Three quaternionic bases with all three pairs unbiased. -/
def unbiasedTriple (U V W : Basis) : Prop := unbiased U V ∧ unbiased U W ∧ unbiased V W
/-- The rank-one orthogonal projector onto the indicated column of a quaternionic unitary basis. -/
def point (U : Basis) (a : Outcome) : QMat := fun i j => U.val i a * star (U.val j a)
/-- The symmetrized matrix product, equal to half the sum of the products in the two orders. -/
def jordan (A B : QMat) : QMat := (1 / 2 : ℝ) • (A * B + B * A)
/-- The real trace of the Jordan product of two quaternionic matrices. -/
def tracePairing (A B : QMat) : ℝ := ∑ i, (jordan A B i i).re
/-- Six times the sum of the squares of the 27 Jordan triple traces of the
basis projectors, with `1/9` subtracted from each trace before squaring. For pairwise unbiased bases
the Solution identifies this formula with the plane projection share through
`QuaternionicMUB.basisGeometricShare_eq_basisS`. -/
def share (U V W : Basis) : ℝ := 6 * ∑ a, ∑ b, ∑ c,
  (tracePairing (jordan (point U a) (point V b)) (point W c) - (1 / 9 : ℝ)) ^ 2
/-- The primitive cubic root of unity \(-1/2+i\sqrt{3}/2\) in the quaternionic complex slice. -/
def ω : Q := ⟨-1 / 2, Real.sqrt 3 / 2, 0, 0⟩
/-- The quaternionic unit \(j\) perpendicular to the chosen complex slice. -/
def j : Q := ⟨0, 0, 1, 0⟩
/-- The three-dimensional Fourier matrix with entries \(\omega^{ab}/\sqrt{3}\). -/
def fourier : QMat := fun a b => (1 / Real.sqrt 3) • ω ^ (a.val * b.val)
/-- A family of quaternions each of unit norm. -/
def unitPhases (p : Outcome → Q) : Prop := ∀ i, Quaternion.normSq (p i) = 1
/-- A common left unitary, independent column permutations and independent right
column phases put the three bases into the identity, the Fourier matrix, and the Fourier matrix
multiplied on the left by the diagonal with entries `p`. The equality clause assumes unit phases `p`. -/
def normalForm (U V W : Basis) (p : Outcome → Q) : Prop :=
  ∃ (L : Basis) (σ τ υ : Equiv.Perm Outcome) (u v w : Outcome → Q),
    unitPhases u ∧ unitPhases v ∧ unitPhases w ∧
    L.val * U.val.submatrix id σ * Matrix.diagonal u = 1 ∧
    L.val * V.val.submatrix id τ * Matrix.diagonal v = fourier ∧
    L.val * W.val.submatrix id υ * Matrix.diagonal w = Matrix.diagonal p * fourier
/-- The explicit left diagonal phases for the third basis in the attaining
triple consisting of the identity, the Fourier matrix, and this diagonally phased Fourier matrix. -/
def attainingPhases : Outcome → Q :=
  let r := Real.sqrt (Real.sqrt 3)
  let A : ℝ := (r + (r ^ 2 - 1) / Real.sqrt 2) / 2
  let C : ℝ := (r - (r ^ 2 - 1) / Real.sqrt 2) / 2
  ![(A : Q) + C • j, ω ^ 2 * ((1 / Real.sqrt 2 : ℝ) • (1 - j)), -(ω * ((C : Q) + A • j))]
/-- The squared norm of the component in the span of \(1,i\) minus the squared norm
of the component in the span of \(j,k\). -/
def balance (q : Q) : ℝ := Complex.normSq ⟨q.re, q.imI⟩ - Complex.normSq ⟨q.imJ, q.imK⟩
/-- A permutation of \((t,0,-t)\) for a real \(t\) with
\(t^2=2\sqrt{3}-3\). Both signs of \(t\) are allowed. -/
def extremalBalance (x y z : ℝ) : Prop :=
  ∃ t : ℝ, t ^ 2 = 2 * Real.sqrt 3 - 3 ∧
    ((x = 0 ∧ y = t ∧ z = -t) ∨ (x = t ∧ y = 0 ∧ z = -t) ∨ (x = t ∧ y = -t ∧ z = 0))

/-- The quaternionic lower bound, its displayed attaining triple, and a necessary condition
for equality in every Fourier normal form. -/
theorem quaternionicLowerBound :
    (∀ U V W : Basis, unbiasedTriple U V W → 1 - 1 / Real.sqrt 3 ≤ share U V W) ∧
    (∃ U V W : Basis, U.val = 1 ∧ V.val = fourier ∧
      W.val = Matrix.diagonal attainingPhases * fourier ∧
      unbiasedTriple U V W ∧ share U V W = 1 - 1 / Real.sqrt 3) ∧
    (∀ U V W : Basis, unbiasedTriple U V W → ∀ p : Outcome → Q, unitPhases p →
      normalForm U V W p → (share U V W = 1 - 1 / Real.sqrt 3 →
        extremalBalance (balance (p 0)) (balance (p 1)) (balance (p 2)))) := by sorry

/-- Every set of pairwise unbiased quaternionic bases has at most five members. -/
theorem quaternionicFiveBound (S : Set Basis) (hS : S.Pairwise unbiased) :
    S.Finite ∧ S.ncard ≤ 5 := by sorry
end Challenge.Quaternionic
