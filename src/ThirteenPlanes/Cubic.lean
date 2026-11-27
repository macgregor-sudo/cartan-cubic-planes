module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.privateInPublic true

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes
noncomputable section

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A real symmetric cubic represented by its metric-raised bilinear product. -/
def symmetricProducts : Submodule ℝ (V →ₗ[ℝ] V →ₗ[ℝ] V) where
  carrier := {μ | (∀ x y, μ x y = μ y x) ∧
    (∀ x y z, ⟪μ x y, z⟫ = ⟪μ x z, y⟫)}
  zero_mem' := by simp
  add_mem' := by
    rintro μ ν ⟨hμc, hμs⟩ ⟨hνc, hνs⟩
    constructor
    · intro x y
      change μ x y + ν x y = μ y x + ν y x
      rw [hμc x y, hνc x y]
    · intro x y z
      change ⟪μ x y + ν x y, z⟫ = ⟪μ x z + ν x z, y⟫
      rw [inner_add_left, inner_add_left, hμs x y z, hνs x y z]
  smul_mem' := by
    rintro r μ ⟨hc, hs⟩
    constructor
    · intro x y
      change r • μ x y = r • μ y x
      rw [hc x y]
    · intro x y z
      change ⟪r • μ x y, z⟫ = ⟪r • μ x z, y⟫
      rw [real_inner_smul_left, real_inner_smul_left, hs x y z]

abbrev SymmetricCubic := ↥(symmetricProducts V)

variable {V}

namespace SymmetricCubic

/-- Build a cubic from a commutative bilinear product with invariant inner product. -/
def ofProduct (μ : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (comm : ∀ x y, μ x y = μ y x)
    (assoc : ∀ x y z, ⟪μ x y, z⟫ = ⟪μ x z, y⟫) : SymmetricCubic V :=
  ⟨μ, comm, assoc⟩

/-- The multiplication operator for a fixed first argument. -/
def L : SymmetricCubic V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V :=
  (symmetricProducts V).subtype

def apply (h : SymmetricCubic V) (x y z : V) : ℝ :=
  ⟪h.L x y, z⟫

def squareMap (h : SymmetricCubic V) (x : V) : V :=
  h.L x x

@[simp] theorem L_ofProduct (μ : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm assoc) :
    (ofProduct μ comm assoc).L = μ := rfl

@[simp] theorem apply_ofProduct (μ : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm assoc) (x y z : V) :
    (ofProduct μ comm assoc).apply x y z = ⟪μ x y, z⟫ := rfl

theorem L_comm (h : SymmetricCubic V) (x y : V) : h.L x y = h.L y x :=
  h.property.1 x y

theorem apply_swap₁₂ (h : SymmetricCubic V) (x y z : V) :
    h.apply x y z = h.apply y x z := by rw [apply, apply, h.L_comm x y]

theorem apply_swap₂₃ (h : SymmetricCubic V) (x y z : V) :
    h.apply x y z = h.apply x z y :=
  h.property.2 x y z

theorem L_isSymmetric (h : SymmetricCubic V) (x : V) : (h.L x).IsSymmetric :=
  fun y z => (h.apply_swap₂₃ x y z).trans (real_inner_comm y (h.L x z))

@[ext] theorem ext {h g : SymmetricCubic V} (eq : ∀ x y z, h.apply x y z = g.apply x y z) :
    h = g :=
  Subtype.ext <| LinearMap.ext fun x => LinearMap.ext fun y => ext_inner_right ℝ (eq x y)

@[simp] theorem apply_zero (x y z : V) : (0 : SymmetricCubic V).apply x y z = 0 := by
  simp [apply]

@[simp] theorem apply_add (h g : SymmetricCubic V) (x y z : V) :
    (h + g).apply x y z = h.apply x y z + g.apply x y z := by
  simp [apply, inner_add_left]

@[simp] theorem apply_smul (a : ℝ) (h : SymmetricCubic V) (x y z : V) :
    (a • h).apply x y z = a * h.apply x y z := by
  simp [apply, real_inner_smul_left]

@[simp] theorem squareMap_add (h g : SymmetricCubic V) (x : V) :
    (h + g).squareMap x = h.squareMap x + g.squareMap x := by simp [squareMap]

@[simp] theorem squareMap_smul (a : ℝ) (h : SymmetricCubic V) (x : V) :
    (a • h).squareMap x = a • h.squareMap x := by simp [squareMap]

@[simp] theorem apply_add₁ (h : SymmetricCubic V) (x x' y z : V) :
    h.apply (x + x') y z = h.apply x y z + h.apply x' y z := by
  simp [apply, inner_add_left]

@[simp] theorem apply_add₂ (h : SymmetricCubic V) (x y y' z : V) :
    h.apply x (y + y') z = h.apply x y z + h.apply x y' z := by
  simp [apply, inner_add_left]

@[simp] theorem apply_add₃ (h : SymmetricCubic V) (x y z z' : V) :
    h.apply x y (z + z') = h.apply x y z + h.apply x y z' := by
  simp [apply, inner_add_right]

@[simp] theorem apply_smul₁ (h : SymmetricCubic V) (a : ℝ) (x y z : V) :
    h.apply (a • x) y z = a * h.apply x y z := by
  simp [apply, real_inner_smul_left]

@[simp] theorem apply_smul₂ (h : SymmetricCubic V) (a : ℝ) (x y z : V) :
    h.apply x (a • y) z = a * h.apply x y z := by
  simp [apply, real_inner_smul_left]

@[simp] theorem apply_smul₃ (h : SymmetricCubic V) (a : ℝ) (x y z : V) :
    h.apply x y (a • z) = a * h.apply x y z := by
  simp [apply, real_inner_smul_right]

section Finite

variable [FiniteDimensional ℝ V]

/-- The real Riesz representation of an algebraic linear functional. -/
noncomputable def riesz : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toLinearEquiv.toLinearMap.comp
    LinearMap.toContinuousLinearMap.toLinearMap

@[simp] theorem inner_riesz (f : V →ₗ[ℝ] ℝ) (z : V) :
    ⟪riesz f, z⟫ = f z :=
  InnerProductSpace.toDual_symm_apply

/-- Build a cubic from the symmetric trilinear polarization of a polynomial. -/
noncomputable def ofPolarization (f : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (comm : ∀ x y z, f x y z = f y x z) (assoc : ∀ x y z, f x y z = f x z y) :
    SymmetricCubic V :=
  ofProduct
    (LinearMap.mk₂ ℝ (fun x y => riesz (f x y))
      (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp))
    (fun x y => ext_inner_right ℝ fun z => by simpa using comm x y z)
    (fun x y z => by simpa using assoc x y z)

@[simp] theorem L_ofPolarization_apply (f : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (comm assoc) (x y : V) : (ofPolarization f comm assoc).L x y = riesz (f x y) := rfl

@[simp] theorem apply_ofPolarization (f : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (comm assoc) (x y z : V) : (ofPolarization f comm assoc).apply x y z = f x y z := by
  simp [ofPolarization]

/-- The coefficients of a cubic in a real orthonormal basis. -/
def coefficient {ι : Type*} [Fintype ι] (h : SymmetricCubic V) (e : OrthonormalBasis ι ℝ V)
    (i j k : ι) : ℝ :=
  h.apply (e i) (e j) (e k)

/-- The trilinear form obtained by lowering the last index. -/
def trilinear (h : SymmetricCubic V) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y =>
    { toFun := h.apply x y
      map_add' := h.apply_add₃ x y
      map_smul' := fun r z => h.apply_smul₃ r x y z })
    (by intros; ext z; exact h.apply_add₁ _ _ _ _)
    (by intros; ext z; exact h.apply_smul₁ _ _ _ _)
    (by intros; ext z; exact h.apply_add₂ _ _ _ _)
    (by intros; ext z; exact h.apply_smul₂ _ _ _ _)

omit [FiniteDimensional ℝ V] in
@[simp] theorem trilinear_apply (h : SymmetricCubic V) (x y z : V) :
    h.trilinear x y z = h.apply x y z := rfl

/-- Pull back all three arguments along the same real linear map. -/
def pullback {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (h : SymmetricCubic V) (f : W →ₗ[ℝ] V) :
    SymmetricCubic W := by
  let g : W →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (h.trilinear (f x) (f y)).comp f)
      (by intros; ext z; simp)
      (by intros; ext z; simp [smul_eq_mul])
      (by intros; ext z; simp)
      (by intros; ext z; simp [smul_eq_mul])
  exact ofPolarization g
    (fun x y z => by
      simpa only [g, LinearMap.mk₂_apply, LinearMap.comp_apply, trilinear_apply] using
        h.apply_swap₁₂ (f x) (f y) (f z))
    (fun x y z => by
      simpa only [g, LinearMap.mk₂_apply, LinearMap.comp_apply, trilinear_apply] using
        h.apply_swap₂₃ (f x) (f y) (f z))

omit [FiniteDimensional ℝ V] in
@[simp] theorem pullback_apply {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (h : SymmetricCubic V) (f : W →ₗ[ℝ] V) (x y z : W) :
    (h.pullback f).apply x y z = h.apply (f x) (f y) (f z) := by
  simp only [pullback, apply_ofPolarization, LinearMap.mk₂_apply, LinearMap.comp_apply,
    trilinear_apply]

private def coefficientForm {ι : Type*} (b : Module.Basis ι ℝ V) (c : ι → ι → ι → ℝ) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  b.constr ℝ fun i => b.constr ℝ fun j => b.constr ℝ fun k => c i j k

omit [FiniteDimensional ℝ V] in
private theorem coefficientForm_basis {ι : Type*} (b : Module.Basis ι ℝ V)
    (c : ι → ι → ι → ℝ) (i j k : ι) : coefficientForm b c (b i) (b j) (b k) = c i j k := by
  simp only [coefficientForm, Module.Basis.constr_basis]

omit [FiniteDimensional ℝ V] in
private theorem coefficientForm_swap₁₂ {ι : Type*} (b : Module.Basis ι ℝ V)
    (c : ι → ι → ι → ℝ) (comm : ∀ i j k, c i j k = c j i k) (x y z : V) :
    coefficientForm b c x y z = coefficientForm b c y x z := by
  let f := coefficientForm b c
  have hf : f = f.flip := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    apply b.ext
    intro k
    simpa only [LinearMap.flip_apply, f, coefficientForm_basis] using comm i j k
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun hf x) y) z

omit [FiniteDimensional ℝ V] in
private theorem coefficientForm_swap₂₃ {ι : Type*} (b : Module.Basis ι ℝ V)
    (c : ι → ι → ι → ℝ) (assoc : ∀ i j k, c i j k = c i k j) (x y z : V) :
    coefficientForm b c x y z = coefficientForm b c x z y := by
  let f := coefficientForm b c
  let flip₂₃ : (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.lflip.toLinearMap
  have hf : f = flip₂₃.comp f := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    apply b.ext
    intro k
    change f (b i) (b j) (b k) = f (b i) (b k) (b j)
    simpa only [f, coefficientForm_basis] using assoc i j k
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun hf x) y) z

/-- Build a cubic from its coefficients in a real orthonormal basis. -/
def ofCoefficients {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (c : ι → ι → ι → ℝ)
    (comm : ∀ i j k, c i j k = c j i k) (assoc : ∀ i j k, c i j k = c i k j) :
    SymmetricCubic V :=
  ofPolarization (coefficientForm e.toBasis c) (coefficientForm_swap₁₂ e.toBasis c comm)
    (coefficientForm_swap₂₃ e.toBasis c assoc)

@[simp] theorem ofCoefficients_apply_basis {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V) (c : ι → ι → ι → ℝ) (comm assoc) (i j k : ι) :
    (ofCoefficients e c comm assoc).apply (e i) (e j) (e k) = c i j k :=
  (apply_ofPolarization _ _ _ _ _ _).trans (coefficientForm_basis e.toBasis c i j k)

omit [FiniteDimensional ℝ V] in
/-- Trace in a real orthonormal basis. -/
theorem trace_eq_sum_inner {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (A : V →ₗ[ℝ] V) : LinearMap.trace ℝ V A = ∑ i, ⟪e i, A (e i)⟫ := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ e.toBasis A, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, e.coe_toBasis_repr_apply,
    e.coe_toBasis, e.repr_apply_apply]

theorem trace_adjoint_eq (A : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ V A.adjoint = LinearMap.trace ℝ V A := by
  simp only [trace_eq_sum_inner (stdOrthonormalBasis ℝ V), LinearMap.adjoint_inner_right]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

/-- The bilinear trace pairing of slices of two cubics. -/
def doublePair (h g : SymmetricCubic V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => LinearMap.trace ℝ V (h.L x * g.L y))
    (by intros; simp [add_mul])
    (by intros; simp [smul_eq_mul])
    (by intros; simp [mul_add])
    (by intros; simp [smul_eq_mul])

/-- The endomorphism formed by contracting two indices of a pair of copies of the cubic. -/
def doubleContraction (h : SymmetricCubic V) : V →ₗ[ℝ] V :=
  riesz.comp (h.doublePair h)

@[simp] theorem inner_doubleContraction (h : SymmetricCubic V) (x y : V) :
    ⟪h.doubleContraction x, y⟫ = LinearMap.trace ℝ V (h.L x * h.L y) :=
  inner_riesz _ _

/-- Trace of the ordered product of three slices. -/
def trianglePair (h g k : SymmetricCubic V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (LinearMap.trace ℝ V).comp
    ((LinearMap.mulLeft ℝ (h.L x * g.L y)).comp k.L))
    (by intros; ext z; simp [add_mul, mul_assoc])
    (by intros; ext z; simp [smul_eq_mul, mul_assoc])
    (by intros; ext z; simp [add_mul, mul_add, mul_assoc])
    (by intros; ext z; simp [smul_eq_mul, mul_assoc])

omit [FiniteDimensional ℝ V] in
@[simp] theorem trianglePair_apply (h g k : SymmetricCubic V) (x y z : V) :
    h.trianglePair g k x y z = LinearMap.trace ℝ V (h.L x * g.L y * k.L z) := rfl

theorem trianglePair_reverse (h g k : SymmetricCubic V) (x y z : V) :
    h.trianglePair g k x y z = k.trianglePair g h z y x := by
  simp only [trianglePair_apply]
  rw [← trace_adjoint_eq (h.L x * g.L y * k.L z)]
  simp only [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    (h.L_isSymmetric x).adjoint_eq, (g.L_isSymmetric y).adjoint_eq,
    (k.L_isSymmetric z).adjoint_eq, LinearMap.comp_assoc]

omit [FiniteDimensional ℝ V] in
theorem trianglePair_cycle (h g k : SymmetricCubic V) (x y z : V) :
    h.trianglePair g k x y z = k.trianglePair h g z x y :=
  LinearMap.trace_mul_cycle ℝ _ _ _

/-- The triangle contraction of three copies of the cubic. -/
def triangleContraction (h : SymmetricCubic V) : SymmetricCubic V :=
  ofPolarization (h.trianglePair h h)
    (fun x y z => (h.trianglePair_cycle h h x y z).trans
      (h.trianglePair_reverse h h z x y))
    (fun x y z => (h.trianglePair_reverse h h x y z).trans
      (h.trianglePair_cycle h h z y x))

@[simp] theorem apply_triangleContraction (h : SymmetricCubic V) (x y z : V) :
    h.triangleContraction.apply x y z =
      LinearMap.trace ℝ V (h.L x * h.L y * h.L z) := by
  simp [triangleContraction]

/-- The coefficient pairing of two cubics, given by the trace of the mixed double contraction. -/
def tensorPairing (h g : SymmetricCubic V) : ℝ :=
  LinearMap.trace ℝ V (riesz.comp (h.doublePair g))

@[simp] theorem tensorPairing_self (h : SymmetricCubic V) :
    h.tensorPairing h = LinearMap.trace ℝ V h.doubleContraction := rfl

def TraceFree (h : SymmetricCubic V) : Prop :=
  ∀ x : V, LinearMap.trace ℝ V (h.L x) = 0

/-- The sum of the insertions of one endomorphism in the three cubic slots. -/
def insert (h : SymmetricCubic V) (A : V →ₗ[ℝ] V) : SymmetricCubic V := by
  let f : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    h.trilinear.comp A + (h.trilinear.flip.comp A).flip +
      h.trilinear.compr₂ (LinearMap.lcomp ℝ ℝ A)
  have ev (x y z) : f x y z = h.apply (A x) y z + h.apply x (A y) z + h.apply x y (A z) := rfl
  exact ofPolarization f
    (fun x y z => by
      rw [ev, ev, h.apply_swap₁₂ (A x) y z, h.apply_swap₁₂ x (A y) z,
        h.apply_swap₁₂ x y (A z)]
      ring)
    (fun x y z => by
      rw [ev, ev, h.apply_swap₂₃ (A x) y z, h.apply_swap₂₃ x (A y) z,
        h.apply_swap₂₃ x y (A z)]
      ring)

@[simp] theorem apply_insert (h : SymmetricCubic V) (A : V →ₗ[ℝ] V) (x y z : V) :
    (h.insert A).apply x y z =
      h.apply (A x) y z + h.apply x (A y) z + h.apply x y (A z) := by
  simp only [insert, apply_ofPolarization]
  rfl

theorem insert_smul_id (h : SymmetricCubic V) (m : ℝ) :
    h.insert (m • (LinearMap.id : V →ₗ[ℝ] V)) = (3 * m) • h := by
  apply ext
  intro x y z
  simp
  ring

omit [FiniteDimensional ℝ V] in
/-- An entry of a multiplication slice in a real orthonormal basis. -/
theorem slice_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) (h : SymmetricCubic V) (x : V) (i j : ι) :
    LinearMap.toMatrix e.toBasis e.toBasis (h.L x) i j = h.apply x (e i) (e j) := by
  rw [LinearMap.toMatrix_apply, e.coe_toBasis_repr_apply, e.repr_apply_apply]
  exact (real_inner_comm _ _).trans (h.apply_swap₂₃ x (e j) (e i))

omit [FiniteDimensional ℝ V] in
theorem doublePair_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (h g : SymmetricCubic V) (x y : V) :
    h.doublePair g x y = ∑ i, ∑ j, h.apply x (e i) (e j) * g.apply y (e i) (e j) := by
  classical
  change LinearMap.trace ℝ V (h.L x * g.L y) = _
  rw [LinearMap.trace_eq_matrix_trace ℝ e.toBasis, LinearMap.toMatrix_mul, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, slice_toMatrix]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [g.apply_swap₂₃ y (e j) (e i)]

theorem inner_doubleContraction_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (h : SymmetricCubic V) (x y : V) :
    ⟪h.doubleContraction x, y⟫ = ∑ i, ∑ j, h.apply x (e i) (e j) * h.apply y (e i) (e j) :=
  (inner_riesz _ _).trans (doublePair_eq_sum e h h x y)

omit [FiniteDimensional ℝ V] in
theorem trianglePair_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (h g k : SymmetricCubic V) (x y z : V) :
    h.trianglePair g k x y z =
      ∑ i, ∑ j, ∑ l, h.apply x (e i) (e j) * g.apply y (e j) (e l) * k.apply z (e l) (e i) := by
  classical
  rw [trianglePair_apply, mul_assoc, LinearMap.trace_eq_matrix_trace ℝ e.toBasis,
    LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, slice_toMatrix, Finset.mul_sum, mul_assoc]

theorem apply_triangleContraction_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (h : SymmetricCubic V) (x y z : V) :
    h.triangleContraction.apply x y z =
      ∑ i, ∑ j, ∑ l, h.apply x (e i) (e j) * h.apply y (e j) (e l) * h.apply z (e l) (e i) := by
  rw [triangleContraction, apply_ofPolarization]
  exact trianglePair_eq_sum e h h h x y z

theorem tensorPairing_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (h g : SymmetricCubic V) :
    h.tensorPairing g = ∑ i, ∑ j, ∑ k, h.coefficient e i j k * g.coefficient e i j k := by
  rw [tensorPairing, trace_eq_sum_inner e]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ⟪e i, riesz (h.doublePair g (e i))⟫ =
    ∑ j, ∑ k, h.apply (e i) (e j) (e k) * g.apply (e i) (e j) (e k)
  rw [real_inner_comm (riesz _) (e i), inner_riesz, doublePair_eq_sum e]

end Finite

end SymmetricCubic

variable (V) in
structure CubicPair where
  diagonalCubic : SymmetricCubic V
  mixingCubic : SymmetricCubic V

/-- The homogeneous two-coupling pencil. -/
def coupling (P : CubicPair V) : (ℝ × ℝ) →ₗ[ℝ] SymmetricCubic V where
  toFun u := u.1 • P.diagonalCubic + u.2 • P.mixingCubic
  map_add' u v := by
    change (u.1 + v.1) • _ + (u.2 + v.2) • _ = _
    simp only [add_smul]
    abel
  map_smul' t u := by
    change (t * u.1) • _ + (t * u.2) • _ = t • _
    rw [mul_smul, mul_smul, smul_add]

@[simp] theorem coupling_apply (P : CubicPair V) (u : ℝ × ℝ) :
    coupling P u = u.1 • P.diagonalCubic + u.2 • P.mixingCubic := rfl

def interactionCubic (P : CubicPair V) (t : ℝ) : SymmetricCubic V :=
  coupling P (1, t)

@[simp] theorem interactionCubic_one (P : CubicPair V) :
    interactionCubic P 1 = P.diagonalCubic + P.mixingCubic := by
  simp [interactionCubic]

theorem coupling_same (P : CubicPair V) (a : ℝ) :
    coupling P (a, a) = a • interactionCubic P 1 := by
  simp [smul_add]

/-- The one-loop tensor vector field in the time `log (μ₀ / μ)`. -/
/- The one-loop beta tensor is based on the equations of Pedro Liendo and Junchen Rong
(arXiv:2107.14515, Eqs. (2.1)–(2.2), p. 5), in the tensor and time conventions
of this development. -/
def oneLoopBeta [FiniteDimensional ℝ V] (ε : ℝ) (h : SymmetricCubic V) :
    SymmetricCubic V :=
  (16 * Real.pi ^ 2)⁻¹ •
    ((8 * Real.pi ^ 2 * ε) • h - (1 / 2 : ℝ) • h.insert h.doubleContraction -
      (2 : ℝ) • h.triangleContraction)

end

end ThirteenPlanes
