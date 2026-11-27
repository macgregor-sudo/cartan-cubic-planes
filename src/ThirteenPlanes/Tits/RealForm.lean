module

public import ThirteenPlanes.Tits.C1Coordinates
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

@[expose] public section

open scoped Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.Tits

noncomputable section

/-- The compact conjugation on the complex first Tits coordinates. -/
def compactInvolution : FirstTits ℂ →ₗ[ℝ] FirstTits ℂ where
  toFun x := (x.1ᴴ, x.2.2ᴴ, x.2.1ᴴ)
  map_add' x y := by
    rcases x with ⟨A, B, C⟩
    rcases y with ⟨A', B', C'⟩
    change ((A + A')ᴴ, (C + C')ᴴ, (B + B')ᴴ) = _
    simp [Matrix.conjTranspose_add]
  map_smul' r x := by
    rcases x with ⟨A, B, C⟩
    change ((r • A)ᴴ, (r • C)ᴴ, (r • B)ᴴ) = _
    simp [Matrix.conjTranspose_smul]

@[simp] theorem compactInvolution_apply (x : FirstTits ℂ) :
    compactInvolution x = (x.1ᴴ, x.2.2ᴴ, x.2.1ᴴ) := rfl

@[simp] theorem compactInvolution_involutive (x : FirstTits ℂ) :
    compactInvolution (compactInvolution x) = x := by
  rcases x with ⟨A, B, C⟩
  simp

theorem compactInvolution_complex_smul (c : ℂ) (x : FirstTits ℂ) :
    compactInvolution (c • x) = star c • compactInvolution x := by
  rcases x with ⟨A, B, C⟩
  change ((c • A)ᴴ, (c • C)ᴴ, (c • B)ᴴ) = _
  simp [Matrix.conjTranspose_smul]

theorem compactInvolution_fixed_iff (x : FirstTits ℂ) :
    compactInvolution x = x ↔ x.1.IsHermitian ∧ x.2.2 = x.2.1ᴴ := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, (congrArg (fun z => z.2.2) h).symm⟩
  · rintro ⟨hA, hC⟩
    rcases x with ⟨A, B, C⟩
    change (Aᴴ, Cᴴ, Bᴴ) = (A, B, C)
    change C = Bᴴ at hC
    subst C
    simp [hA.eq]

/-- The real subspace fixed by compact conjugation. -/
def compactTitsSubspace : Submodule ℝ (FirstTits ℂ) :=
  LinearMap.ker (compactInvolution - LinearMap.id)

/-- The fixed real form, equipped separately with its trace metric. -/
def CompactTits := ↥compactTitsSubspace

instance : AddCommGroup CompactTits := inferInstanceAs (AddCommGroup ↥compactTitsSubspace)
instance : Module ℝ CompactTits := inferInstanceAs (Module ℝ ↥compactTitsSubspace)
instance : FiniteDimensional ℝ CompactTits :=
  inferInstanceAs (FiniteDimensional ℝ ↥compactTitsSubspace)

theorem trace3_eq_matrixTrace (A : Mat3 ℂ) : trace3 A = Matrix.trace A := by
  simp [trace3, Matrix.trace, Fin.sum_univ_three]

@[simp] theorem trace3_adjoint (A : Mat3 ℂ) : trace3 Aᴴ = star (trace3 A) := by
  simp only [trace3_eq_matrixTrace, Matrix.trace_conjTranspose]

theorem adjugate3_adjoint (A : Mat3 ℂ) : adjugate3 Aᴴ = (adjugate3 A)ᴴ := by
  ext i j
  change adjugate3 Aᴴ i j = star (adjugate3 A j i)
  fin_cases i <;> fin_cases j <;>
    simp [adjugate3, Matrix.conjTranspose_apply] <;> ring

/-- Compact conjugation intertwines the complex Jordan square. -/
theorem compactInvolution_square (x : FirstTits ℂ) :
    compactInvolution (firstTitsSquare x) = firstTitsSquare (compactInvolution x) := by
  rcases x with ⟨A, B, C⟩
  simp only [compactInvolution_apply, firstTitsSquare, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, ← trace3_adjoint, ← adjugate3_adjoint]

namespace CompactTits

def coordinates : CompactTits →ₗ[ℝ] FirstTits ℂ :=
  compactTitsSubspace.subtype

@[ext] theorem ext {x y : CompactTits} (h : coordinates x = coordinates y) : x = y :=
  compactTitsSubspace.subtype_injective h

theorem fixed (x : CompactTits) : compactInvolution (coordinates x) = coordinates x := by
  exact sub_eq_zero.mp x.property

theorem hermitian (x : CompactTits) : (coordinates x).1.IsHermitian :=
  (compactInvolution_fixed_iff _).mp (fixed x) |>.1

theorem third_eq_adjoint (x : CompactTits) : (coordinates x).2.2 = (coordinates x).2.1ᴴ :=
  (compactInvolution_fixed_iff _).mp (fixed x) |>.2

def ofFixed (x : FirstTits ℂ) (hx : compactInvolution x = x) : CompactTits :=
  ⟨x, sub_eq_zero.mpr hx⟩

@[simp] theorem coordinates_ofFixed (x : FirstTits ℂ) (hx : compactInvolution x = x) :
    coordinates (ofFixed x hx) = x := rfl

/-- Placement of Hermitian A and arbitrary B in the fixed coordinate form. -/
def ofMatrices (A B : Mat3 ℂ) (hA : A.IsHermitian) : CompactTits :=
  ofFixed (A, B, Bᴴ) ((compactInvolution_fixed_iff _).mpr ⟨hA, rfl⟩)

@[simp] theorem coordinates_ofMatrices (A B : Mat3 ℂ) (hA : A.IsHermitian) :
    coordinates (ofMatrices A B hA) = (A, B, Bᴴ) := rfl

def one : CompactTits :=
  ofMatrices 1 0 (by simp)

@[simp] theorem coordinates_one : coordinates one = firstTitsOne := by
  simp [one, firstTitsOne]

def square (x : CompactTits) : CompactTits :=
  ofFixed (firstTitsSquare (coordinates x)) (by rw [compactInvolution_square, fixed])

@[simp] theorem coordinates_square (x : CompactTits) :
    coordinates (square x) = firstTitsSquare (coordinates x) := rfl

/-- The polarized compact Jordan product. -/
def product (x y : CompactTits) : CompactTits :=
  (1 / 2 : ℝ) • (square (x + y) - square x - square y)

@[simp] theorem coordinates_product (x y : CompactTits) :
    coordinates (product x y) =
      (1 / 2 : ℝ) •
        (firstTitsSquare (coordinates x + coordinates y) - firstTitsSquare (coordinates x) -
          firstTitsSquare (coordinates y)) := by
  simp [product]

theorem coordinates_product_eq_polar (x y : CompactTits) :
    coordinates (product x y) = polarProduct firstTitsSquare (coordinates x) (coordinates y) := by
  rw [coordinates_product, polarProduct, invOf_eq_inv]
  let w : FirstTits ℂ := firstTitsSquare (coordinates x + coordinates y) -
    firstTitsSquare (coordinates x) - firstTitsSquare (coordinates y)
  change (1 / 2 : ℝ) • w = (2 : ℂ)⁻¹ • w
  have h : ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by norm_num [div_eq_mul_inv]
  rw [← h]
  rfl

/-- Real trace of the first matrix coordinate. -/
def trace : CompactTits →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((Matrix.traceLinearMap (Fin 3) ℝ ℂ).comp
    ((LinearMap.fst ℝ (Mat3 ℂ) (Mat3 ℂ × Mat3 ℂ)).comp coordinates))

@[simp] theorem trace_apply (x : CompactTits) : trace x = (trace3 (coordinates x).1).re := by
  simp [trace, trace3_eq_matrixTrace]

theorem complex_trace_eq (x : CompactTits) :
    (trace x : ℂ) = trace3 (coordinates x).1 := by
  have h := trace3_adjoint (coordinates x).1
  rw [(hermitian x).eq] at h
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  apply Complex.ext
  · simp
  · simpa using (show 0 = (trace3 (coordinates x).1).im by linarith)

@[simp] theorem trace_one : trace one = 3 := by
  simp [trace_apply, firstTitsOne, trace3_eq_matrixTrace]

end CompactTits

/-- The traceless subspace of the compact real form. -/
def compactTitsTracelessSubspace : Submodule ℝ CompactTits :=
  LinearMap.ker CompactTits.trace

abbrev CompactTitsTraceless := ↥compactTitsTracelessSubspace

namespace CompactTits

/-- The trace-free projection along the unit. -/
def center (x : CompactTits) : CompactTitsTraceless :=
  ⟨x - (trace x / 3) • one, by
    change trace (x - (trace x / 3) • one) = 0
    simp only [map_sub, map_smul, trace_one, smul_eq_mul]
    ring⟩

end CompactTits

namespace CompactTitsTraceless

def coordinates : CompactTitsTraceless →ₗ[ℝ] FirstTits ℂ :=
  CompactTits.coordinates.comp compactTitsTracelessSubspace.subtype

def ofMatrices (A B : Mat3 ℂ) (hA : A.IsHermitian) (htr : trace3 A = 0) :
    CompactTitsTraceless :=
  ⟨CompactTits.ofMatrices A B hA, by
    change CompactTits.trace (CompactTits.ofMatrices A B hA) = 0
    simp [htr]⟩

@[simp] theorem coordinates_ofMatrices (A B : Mat3 ℂ) (hA htr) :
    coordinates (ofMatrices A B hA htr) = (A, B, Bᴴ) := rfl

@[simp] theorem trace_zero (x : CompactTitsTraceless) : CompactTits.trace x.val = 0 :=
  x.property

@[simp] theorem complex_trace_zero (x : CompactTitsTraceless) :
    trace3 (coordinates x).1 = 0 := by
  change trace3 (CompactTits.coordinates x.val).1 = 0
  rw [← CompactTits.complex_trace_eq, trace_zero, Complex.ofReal_zero]

/-- The square projected to the traceless compact slice. -/
def square (x : CompactTitsTraceless) : CompactTitsTraceless :=
  CompactTits.center (CompactTits.square x.val)

@[simp] theorem coordinates_square (x : CompactTitsTraceless) :
    coordinates (square x) = firstTitsSquare (coordinates x) -
      (CompactTits.trace (CompactTits.square x.val) / 3) • (firstTitsOne : FirstTits ℂ) := by
  change CompactTits.coordinates (_ - _ • CompactTits.one) = _
  simp [coordinates]

end CompactTitsTraceless

end

end ThirteenPlanes.Tits
