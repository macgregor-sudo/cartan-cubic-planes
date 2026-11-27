module

public import ThirteenPlanes.NativeFramesCarrier

@[expose] public section

set_option backward.privateInPublic true

/-! The complexification of the compact Albert algebra.

Elements are pairs `x + i y` in `Glennie.Albert`. The Jordan product is complex-bilinear,
`conj` fixes the real algebra, and `mapC` extends a real-linear endomorphism.
The definitions are copied from `Grading.JC` in the same development.
The two models agree through the identity on their pairs. -/

namespace ThirteenPlanes.AlbertGrading.Recut

open Glennie

noncomputable section

/-- An element `re + i im` of the complexified Albert algebra. -/
@[ext] structure JC where
  re : Glennie.Albert
  im : Glennie.Albert

namespace JC

/-- The underlying pair. -/
def toProd : JC ≃ Glennie.Albert × Glennie.Albert where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup JC := toProd.addCommGroup

@[simp] theorem add_re (z w : JC) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : JC) : (z + w).im = z.im + w.im := rfl
@[simp] theorem zero_re : (0 : JC).re = 0 := rfl
@[simp] theorem zero_im : (0 : JC).im = 0 := rfl

instance : SMul ℂ JC := ⟨fun c z => ⟨c.re • z.re - c.im • z.im, c.re • z.im + c.im • z.re⟩⟩

@[simp] theorem smul_re (c : ℂ) (z : JC) : (c • z).re = c.re • z.re - c.im • z.im := rfl
@[simp] theorem smul_im (c : ℂ) (z : JC) : (c • z).im = c.re • z.im + c.im • z.re := rfl

private theorem one_smul' (z : JC) : (1 : ℂ) • z = z := by apply JC.ext <;> simp

private theorem mul_smul' (a b : ℂ) (z : JC) : (a * b) • z = a • b • z := by
  apply JC.ext
  · rw [smul_re, smul_re, smul_re, smul_im, Complex.mul_re, Complex.mul_im]; module
  · rw [smul_im, smul_im, smul_re, smul_im, Complex.mul_re, Complex.mul_im]; module

private theorem smul_zero' (a : ℂ) : a • (0 : JC) = 0 := by apply JC.ext <;> simp

private theorem smul_add' (a : ℂ) (z w : JC) : a • (z + w) = a • z + a • w := by
  apply JC.ext
  · rw [smul_re, add_re, add_re, add_im, smul_re, smul_re]; module
  · rw [smul_im, add_re, add_im, add_im, smul_im, smul_im]; module

private theorem add_smul' (a b : ℂ) (z : JC) : (a + b) • z = a • z + b • z := by
  apply JC.ext
  · rw [smul_re, add_re, smul_re, smul_re, Complex.add_re, Complex.add_im]; module
  · rw [smul_im, add_im, smul_im, smul_im, Complex.add_re, Complex.add_im]; module

private theorem zero_smul' (z : JC) : (0 : ℂ) • z = 0 := by apply JC.ext <;> simp

instance : Module ℂ JC where
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_zero := smul_zero'
  smul_add := smul_add'
  add_smul := add_smul'
  zero_smul := zero_smul'

@[simp] theorem real_smul_re (r : ℝ) (z : JC) : (r • z).re = r • z.re := by
  have h : (r • z) = (r : ℂ) • z := rfl
  rw [h, smul_re, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

@[simp] theorem real_smul_im (r : ℝ) (z : JC) : (r • z).im = r • z.im := by
  have h : (r • z) = (r : ℂ) • z := rfl
  rw [h, smul_im, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-- The inclusion of the real form. -/
def of (x : Glennie.Albert) : JC := ⟨x, 0⟩

@[simp] theorem of_re (x : Glennie.Albert) : (of x).re = x := rfl
@[simp] theorem of_im (x : Glennie.Albert) : (of x).im = 0 := rfl

theorem of_add (x y : Glennie.Albert) : of (x + y) = of x + of y := by apply JC.ext <;> simp
theorem of_smul (r : ℝ) (x : Glennie.Albert) : of (r • x) = r • of x := by apply JC.ext <;> simp

/-- The real inclusion as a real-linear map. -/
def ofLinear : Glennie.Albert →ₗ[ℝ] JC where
  toFun := of
  map_add' := of_add
  map_smul' := of_smul

/-- The conjugation fixing the real form. -/
def conj (z : JC) : JC := ⟨z.re, -z.im⟩

/-- The complex-bilinear extension of the Jordan product. -/
def mul (z w : JC) : JC :=
  ⟨jordan z.re w.re - jordan z.im w.im, jordan z.re w.im + jordan z.im w.re⟩

/-- The unit `e`. -/
def one : JC := of 1

/-- The complex-linear extension of a real-linear endomorphism. -/
def mapC (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert) : JC →ₗ[ℂ] JC where
  toFun z := ⟨f z.re, f z.im⟩
  map_add' z w := by apply JC.ext <;> simp
  map_smul' c z := by apply JC.ext <;> simp

end JC

end

end ThirteenPlanes.AlbertGrading.Recut
