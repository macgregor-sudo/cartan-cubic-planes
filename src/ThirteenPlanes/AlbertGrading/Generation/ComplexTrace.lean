module

public import ThirteenPlanes.AlbertGrading.Generation.Transport

@[expose] public section

/-! A unital Jordan homomorphism from the complex Hermitian matrices into the compact Albert algebra
preserves traces. Peirce argument: the images of the diagonal matrix units are orthogonal
idempotents of equal trace (exchanged through `E_{ab} + E_{ba}`), and every half-Peirce component
is traceless, by associativity of the trace form. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open scoped Matrix

local notation "CM" => Matrix (Fin 3) (Fin 3) ℂ

/-! ### Albert-side Peirce facts -/

theorem trace_eq_zero_of_half {f y : Glennie.Albert} (hf : Glennie.jordan f f = f)
    (hy : Glennie.jordan f y = (1 / 2 : ℝ) • y) : Glennie.trace y = 0 := by
  have h1 : Glennie.inner f y = (1 / 2 : ℝ) * Glennie.trace y := by
    change Glennie.trace (Glennie.jordan f y) = _
    rw [hy, Glennie.trace_smul]
  have h2 : Glennie.inner f y = (1 / 2 : ℝ) * Glennie.inner f y := by
    calc Glennie.inner f y = Glennie.inner (Glennie.jordan f f) y := by rw [hf]
      _ = Glennie.inner f (Glennie.jordan f y) := Glennie.inner_jordan_associative f f y
      _ = (1 / 2 : ℝ) * Glennie.inner f y := by rw [hy, Glennie.inner_smul_right]
  have h3 : Glennie.inner f y = 0 := by linarith
  rw [h3] at h1
  linarith

theorem trace_eq_of_exchange {f g s : Glennie.Albert} (hf : Glennie.jordan f f = f)
    (hfg : Glennie.jordan f g = 0) (hs : Glennie.jordan s s = f + g)
    (hfs : Glennie.jordan f s = (1 / 2 : ℝ) • s) : Glennie.trace f = Glennie.trace g := by
  have h1 : Glennie.inner f (Glennie.jordan s s) = Glennie.trace f := by
    change Glennie.trace (Glennie.jordan f (Glennie.jordan s s)) = _
    rw [hs, Glennie.jordan_add_right, hf, hfg, add_zero]
  have h2 : Glennie.inner f (Glennie.jordan s s) =
      (1 / 2 : ℝ) * (Glennie.trace f + Glennie.trace g) := by
    rw [← Glennie.inner_jordan_associative, hfs, Glennie.inner_smul_left]
    change (1 / 2 : ℝ) * Glennie.trace (Glennie.jordan s s) = _
    rw [hs, Glennie.trace_add]
  linarith

/-! ### Matrix-side elements -/

/-- The half-anticommutator of two complex Hermitian matrices. -/
def cjordan (x y : ComplexHermitian3) : ComplexHermitian3 :=
  ⟨(1 / 2 : ℝ) • ((x : CM) * y + y * x), by
    rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial,
      selfAdjoint.mem_iff.mp x.2, selfAdjoint.mem_iff.mp y.2, add_comm]⟩

/-- The diagonal matrix unit `E_aa`. -/
def unitE (a : Fin 3) : ComplexHermitian3 :=
  ⟨Matrix.single a a 1, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]⟩

/-- The exchange element `E_ab + E_ba`. -/
def unitS (a b : Fin 3) : ComplexHermitian3 :=
  ⟨Matrix.single a b 1 + Matrix.single b a 1, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_add,
      Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, add_comm]⟩

theorem single_ne {i j k l : Fin 3} (h : j ≠ k) :
    (Matrix.single i j (1 : ℂ) : CM) * Matrix.single k l 1 = 0 :=
  Matrix.single_mul_single_of_ne 1 i j k h 1

@[simp] theorem unitE_coe (a : Fin 3) : (unitE a : CM) = Matrix.single a a 1 := rfl
@[simp] theorem unitS_coe (a b : Fin 3) :
    (unitS a b : CM) = Matrix.single a b 1 + Matrix.single b a 1 := rfl
@[simp] theorem cjordan_coe (x y : ComplexHermitian3) :
    (cjordan x y : CM) = (1 / 2 : ℝ) • ((x : CM) * y + y * x) := rfl

theorem cjordan_EE (a : Fin 3) : cjordan (unitE a) (unitE a) = unitE a := by
  apply Subtype.ext
  simp only [cjordan_coe, unitE_coe, Matrix.single_mul_single_same, mul_one]
  module

theorem cjordan_EE_ne {a b : Fin 3} (h : a ≠ b) : cjordan (unitE a) (unitE b) = 0 := by
  apply Subtype.ext
  simp [single_ne h, single_ne (Ne.symm h)]

theorem cjordan_SS {a b : Fin 3} (h : a ≠ b) :
    cjordan (unitS a b) (unitS a b) = unitE a + unitE b := by
  apply Subtype.ext
  simp only [cjordan_coe, unitS_coe, unitE_coe, AddSubgroup.coe_add, add_mul, mul_add,
    Matrix.single_mul_single_same, single_ne h,
    single_ne (Ne.symm h), mul_one, zero_add, add_zero]
  module

theorem cjordan_ES {a b : Fin 3} (h : a ≠ b) :
    cjordan (unitE a) (unitS a b) = (1 / 2 : ℝ) • unitS a b := by
  apply Subtype.ext
  simp only [cjordan_coe, unitS_coe, unitE_coe, add_mul, mul_add,
    Matrix.single_mul_single_same, single_ne h,
    single_ne (Ne.symm h), mul_one, zero_add, add_zero,
    selfAdjoint.val_smul]

theorem single_sum_one :
    (Matrix.single 0 0 1 + Matrix.single 1 1 1 + Matrix.single 2 2 1 : CM) = 1 := by
  have h := Matrix.sum_single_one (α := ℂ) (m := Fin 3)
  rw [Fin.sum_univ_three] at h
  exact h

theorem sum_unitE : (unitE 0 + unitE 1 + unitE 2 : ComplexHermitian3) = 1 := by
  apply Subtype.ext
  exact single_sum_one

theorem diag_real (x : ComplexHermitian3) (a : Fin 3) :
    (x : CM) a a = (((x : CM) a a).re : ℂ) := by
  have hx : star (x : CM) = x := selfAdjoint.mem_iff.mp x.2
  have h := congrFun (congrFun hx a) a
  rw [Matrix.star_apply] at h
  exact (Complex.conj_eq_iff_re.mp h).symm

/-- The half-Peirce component `x ∘ E_aa - x_aa E_aa`. -/
def halfPart (x : ComplexHermitian3) (a : Fin 3) : ComplexHermitian3 :=
  cjordan x (unitE a) - ((x : CM) a a).re • unitE a

theorem cjordan_E_half (x : ComplexHermitian3) (a : Fin 3) :
    cjordan (unitE a) (halfPart x a) = (1 / 2 : ℝ) • halfPart x a := by
  apply Subtype.ext
  set s : CM := Matrix.single a a 1
  set X : CM := (x : CM)
  set r : ℝ := (X a a).re
  have hss : s * s = s := by simp [s]
  have hxss : X * s * s = X * s := by rw [mul_assoc, hss]
  have hsxs : s * X * s = r • s := by
    simp only [s, Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single]
    congr 1
    rw [Complex.real_smul, mul_one]
    exact diag_real x a
  change (1 / 2 : ℝ) • (s * ((1 / 2 : ℝ) • (X * s + s * X) - r • s) +
      ((1 / 2 : ℝ) • (X * s + s * X) - r • s) * s) =
    (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (X * s + s * X) - r • s)
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, ← mul_assoc,
    hss, hxss, hsxs]
  module

theorem cjordan_sum_E (x : ComplexHermitian3) :
    cjordan x (unitE 0) + cjordan x (unitE 1) + cjordan x (unitE 2) = x := by
  apply Subtype.ext
  set X : CM := (x : CM)
  change (1 / 2 : ℝ) • (X * Matrix.single 0 0 1 + Matrix.single 0 0 1 * X) +
      (1 / 2 : ℝ) • (X * Matrix.single 1 1 1 + Matrix.single 1 1 1 * X) +
      (1 / 2 : ℝ) • (X * Matrix.single 2 2 1 + Matrix.single 2 2 1 * X) = X
  have key : (1 / 2 : ℝ) • (X * Matrix.single 0 0 1 + Matrix.single 0 0 1 * X) +
      (1 / 2 : ℝ) • (X * Matrix.single 1 1 1 + Matrix.single 1 1 1 * X) +
      (1 / 2 : ℝ) • (X * Matrix.single 2 2 1 + Matrix.single 2 2 1 * X) =
      (1 / 2 : ℝ) • (X * (Matrix.single 0 0 1 + Matrix.single 1 1 1 + Matrix.single 2 2 1) +
        (Matrix.single 0 0 1 + Matrix.single 1 1 1 + Matrix.single 2 2 1) * X) := by
    rw [mul_add, mul_add, add_mul, add_mul]
    module
  rw [key, single_sum_one, mul_one, one_mul]
  module

/-! ### Trace preservation -/

/-- A unit-preserving Jordan homomorphism from `H₃(ℂ)` into the Albert algebra carries the real
matrix trace to the Albert trace. -/
theorem trace_of_complex_jordan_hom (φ : ComplexHermitian3 →ₗ[ℝ] Glennie.Albert) (hunit : φ 1 = 1)
    (hprod : ∀ x y z : ComplexHermitian3,
      (z : CM) = (1 / 2 : ℝ) • ((x : CM) * y + y * x) → φ z = Glennie.jordan (φ x) (φ y))
    (x : ComplexHermitian3) : Glennie.trace (φ x) = (Matrix.trace (x : CM)).re := by
  have hj (u v : ComplexHermitian3) : φ (cjordan u v) = Glennie.jordan (φ u) (φ v) :=
    hprod u v _ rfl
  have idem (a : Fin 3) : Glennie.jordan (φ (unitE a)) (φ (unitE a)) = φ (unitE a) := by
    rw [← hj, cjordan_EE]
  have orth {a b : Fin 3} (h : a ≠ b) :
      Glennie.jordan (φ (unitE a)) (φ (unitE b)) = 0 := by
    rw [← hj, cjordan_EE_ne h, map_zero]
  have exch {a b : Fin 3} (h : a ≠ b) :
      Glennie.trace (φ (unitE a)) = Glennie.trace (φ (unitE b)) := by
    apply trace_eq_of_exchange (idem a) (orth h) (s := φ (unitS a b))
    · rw [← hj, cjordan_SS h, map_add]
    · rw [← hj, cjordan_ES h, map_smul]
  have hsum : Glennie.trace (φ (unitE 0)) + Glennie.trace (φ (unitE 1)) +
      Glennie.trace (φ (unitE 2)) = 3 := by
    rw [← Glennie.trace_add, ← Glennie.trace_add, ← map_add, ← map_add, sum_unitE, hunit,
      Glennie.trace_unit]
  have e01 := exch (show (0 : Fin 3) ≠ 1 by decide)
  have e02 := exch (show (0 : Fin 3) ≠ 2 by decide)
  have hE (a : Fin 3) : Glennie.trace (φ (unitE a)) = 1 := by
    fin_cases a
    · change Glennie.trace (φ (unitE 0)) = 1; linarith
    · change Glennie.trace (φ (unitE 1)) = 1; linarith
    · change Glennie.trace (φ (unitE 2)) = 1; linarith
  have hpart (a : Fin 3) :
      Glennie.trace (φ (cjordan x (unitE a))) = ((x : CM) a a).re := by
    have hsplit : cjordan x (unitE a) = ((x : CM) a a).re • unitE a + halfPart x a := by
      simp [halfPart]
    have hhalf : Glennie.trace (φ (halfPart x a)) = 0 := by
      apply trace_eq_zero_of_half (idem a)
      rw [← hj, cjordan_E_half, map_smul]
    rw [hsplit, map_add, map_smul, Glennie.trace_add, Glennie.trace_smul, hE, hhalf]
    ring
  conv_lhs => rw [← cjordan_sum_E x]
  rw [map_add, map_add, Glennie.trace_add, Glennie.trace_add, hpart, hpart,
    hpart, Matrix.trace, Fin.sum_univ_three]
  simp [Matrix.diag]

end ThirteenPlanes.AlbertGrading
