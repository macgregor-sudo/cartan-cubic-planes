module

public import ThirteenPlanes.NativeFramesCarrier

@[expose] public section

set_option backward.privateInPublic true

/-! # The complexification of the compact Albert algebra

`J_ℂ = J ⊗ ℂ` is modelled by pairs `x + i y` of elements of the native compact carrier
`Glennie.Albert`. The Jordan product, the trace and the trace form are extended
complex-bilinearly, and `conj` is the conjugation fixing `J`. -/

namespace ThirteenPlanes.AlbertGrading.Grading

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
@[simp] theorem neg_re (z : JC) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : JC) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : JC) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : JC) : (z - w).im = z.im - w.im := rfl

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
theorem of_sub (x y : Glennie.Albert) : of (x - y) = of x - of y := by apply JC.ext <;> simp
theorem of_smul (r : ℝ) (x : Glennie.Albert) : of (r • x) = r • of x := by apply JC.ext <;> simp
theorem of_zero : of 0 = 0 := by apply JC.ext <;> simp

theorem of_injective : Function.Injective of := fun _ _ h => congrArg re h

/-- The real inclusion as a real-linear map. -/
def ofLinear : Glennie.Albert →ₗ[ℝ] JC where
  toFun := of
  map_add' := of_add
  map_smul' := of_smul

@[simp] theorem ofLinear_apply (x : Glennie.Albert) : ofLinear x = of x := rfl

/-- Every element is `of re + i • of im`. -/
theorem eq_re_add_im (z : JC) : z = of z.re + Complex.I • of z.im := by
  apply JC.ext <;> simp

/-- The conjugation fixing the real form. -/
def conj (z : JC) : JC := ⟨z.re, -z.im⟩

@[simp] theorem conj_re (z : JC) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : JC) : (conj z).im = -z.im := rfl
@[simp] theorem conj_conj (z : JC) : conj (conj z) = z := by apply JC.ext <;> simp
@[simp] theorem conj_of (x : Glennie.Albert) : conj (of x) = of x := by apply JC.ext <;> simp
theorem conj_add (z w : JC) : conj (z + w) = conj z + conj w := by apply JC.ext <;> simp [add_comm]
theorem conj_sub (z w : JC) : conj (z - w) = conj z - conj w := by apply JC.ext <;> simp; abel
theorem conj_neg (z : JC) : conj (-z) = -conj z := by apply JC.ext <;> simp
theorem conj_zero : conj 0 = 0 := by apply JC.ext <;> simp
theorem conj_smul (c : ℂ) (z : JC) : conj (c • z) = star c • conj z := by
  apply JC.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> abel
theorem conj_injective : Function.Injective conj := fun z w h => by
  rw [← conj_conj z, h, conj_conj]

theorem conj_eq_self_iff (z : JC) : conj z = z ↔ z = of z.re := by
  constructor
  · intro h
    apply JC.ext
    · rfl
    · have := congrArg im h
      simp only [conj_im] at this
      simp only [of_im]
      have h2 : (2 : ℝ) • z.im = 0 := by rw [two_smul]; nth_rewrite 1 [← this]; simp
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro h; rw [h, conj_of]

/-- The complex-bilinear extension of the Jordan product. -/
def mul (z w : JC) : JC :=
  ⟨jordan z.re w.re - jordan z.im w.im, jordan z.re w.im + jordan z.im w.re⟩

@[simp] theorem mul_re (z w : JC) : (mul z w).re = jordan z.re w.re - jordan z.im w.im := rfl
@[simp] theorem mul_im (z w : JC) : (mul z w).im = jordan z.re w.im + jordan z.im w.re := rfl

theorem mul_comm (z w : JC) : mul z w = mul w z := by
  apply JC.ext <;> simp [jordan_comm z.re, jordan_comm z.im] ; abel

theorem mul_add_left (z z' w : JC) : mul (z + z') w = mul z w + mul z' w := by
  apply JC.ext <;> simp [jordan_add_left] <;> abel

theorem mul_add_right (z w w' : JC) : mul z (w + w') = mul z w + mul z w' := by
  rw [mul_comm, mul_add_left, mul_comm w, mul_comm w']

theorem mul_smul_left (c : ℂ) (z w : JC) : mul (c • z) w = c • mul z w := by
  apply JC.ext <;> simp [jordan_sub_left, jordan_add_left, jordan_smul_left, smul_sub, smul_add] <;> abel

theorem mul_smul_right (c : ℂ) (z w : JC) : mul z (c • w) = c • mul z w := by
  rw [mul_comm, mul_smul_left, mul_comm]

theorem mul_sub_left (z z' w : JC) : mul (z - z') w = mul z w - mul z' w := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add_left, ← neg_one_smul ℂ z', mul_smul_left,
    neg_one_smul]

theorem mul_sub_right (z w w' : JC) : mul z (w - w') = mul z w - mul z w' := by
  rw [mul_comm, mul_sub_left, mul_comm w, mul_comm w']

@[simp] theorem mul_zero_left (w : JC) : mul 0 w = 0 := by apply JC.ext <;> simp
@[simp] theorem mul_zero_right (z : JC) : mul z 0 = 0 := by apply JC.ext <;> simp

theorem of_mul (x y : Glennie.Albert) : mul (of x) (of y) = of (jordan x y) := by
  apply JC.ext <;> simp

theorem conj_mul (z w : JC) : conj (mul z w) = mul (conj z) (conj w) := by
  apply JC.ext <;> simp [jordan_neg_left, jordan_neg_right] ; abel

/-- The unit `e`. -/
def one : JC := of 1

theorem one_mul (z : JC) : mul one z = z := by apply JC.ext <;> simp [one]
theorem mul_one (z : JC) : mul z one = z := by rw [mul_comm, one_mul]
@[simp] theorem conj_one : conj one = one := conj_of 1

theorem one_ne_zero : one ≠ 0 := by
  intro h
  have := congrArg (fun z => trace z.re) h
  simp [one] at this

/-- The complex-bilinear extension of the trace form. -/
def ip (z w : JC) : ℂ :=
  ⟨inner z.re w.re - inner z.im w.im, inner z.re w.im + inner z.im w.re⟩

@[simp] theorem ip_re (z w : JC) : (ip z w).re = inner z.re w.re - inner z.im w.im := rfl
@[simp] theorem ip_im (z w : JC) : (ip z w).im = inner z.re w.im + inner z.im w.re := rfl

theorem ip_comm (z w : JC) : ip z w = ip w z := by
  apply Complex.ext <;> simp [Glennie.inner_comm z.re, Glennie.inner_comm z.im] ; ring

theorem ip_add_left (z z' w : JC) : ip (z + z') w = ip z w + ip z' w := by
  apply Complex.ext <;> simp [inner_add_left] <;> ring

theorem ip_add_right (z w w' : JC) : ip z (w + w') = ip z w + ip z w' := by
  rw [ip_comm, ip_add_left, ip_comm w, ip_comm w']

theorem ip_smul_left (c : ℂ) (z w : JC) : ip (c • z) w = c * ip z w := by
  apply Complex.ext <;>
    simp [inner_sub_left, inner_add_left, inner_smul_left, Complex.mul_re, Complex.mul_im] <;> ring

theorem ip_smul_right (c : ℂ) (z w : JC) : ip z (c • w) = c * ip z w := by
  rw [ip_comm, ip_smul_left, ip_comm]

theorem ip_sub_left (z z' w : JC) : ip (z - z') w = ip z w - ip z' w := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ip_add_left, ← neg_one_smul ℂ z', ip_smul_left]; ring

theorem ip_sub_right (z w w' : JC) : ip z (w - w') = ip z w - ip z w' := by
  rw [ip_comm, ip_sub_left, ip_comm w, ip_comm w']

@[simp] theorem ip_zero_left (w : JC) : ip 0 w = 0 := by apply Complex.ext <;> simp
@[simp] theorem ip_zero_right (z : JC) : ip z 0 = 0 := by apply Complex.ext <;> simp

theorem ip_of (x y : Glennie.Albert) : ip (of x) (of y) = (inner x y : ℂ) := by
  apply Complex.ext <;> simp

theorem ip_conj (z w : JC) : ip (conj z) (conj w) = star (ip z w) := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] ; ring

/-- Associativity of the trace form. -/
theorem ip_mul_assoc (x y z : JC) : ip (mul x y) z = ip x (mul y z) := by
  apply Complex.ext <;>
    simp [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
      inner_jordan_associative] <;> ring

/-- The Hermitian form `⟨z, z̄⟩` is the real squared length of the two components. -/
theorem ip_conj_self (z : JC) :
    ip z (conj z) = ((inner z.re z.re + inner z.im z.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Glennie.inner_comm z.im z.re]

theorem ip_conj_self_pos {z : JC} (hz : z ≠ 0) : 0 < (ip z (conj z)).re := by
  rw [ip_conj_self, Complex.ofReal_re]
  have h1 := inner_self_nonneg z.re
  have h2 := inner_self_nonneg z.im
  by_contra hle
  have e1 : inner z.re z.re = 0 := by linarith
  have e2 : inner z.im z.im = 0 := by linarith
  exact hz (JC.ext ((inner_self_eq_zero _).mp e1) ((inner_self_eq_zero _).mp e2))

theorem ip_conj_self_im (z : JC) : (ip z (conj z)).im = 0 := by
  rw [ip_conj_self, Complex.ofReal_im]

/-- The complex trace. -/
def tr (z : JC) : ℂ := ⟨trace z.re, trace z.im⟩

theorem ip_one_right (z : JC) : ip z one = tr z := by
  apply Complex.ext <;> simp [one, tr, Glennie.inner, Glennie.trace]

theorem ip_one_left (z : JC) : ip one z = tr z := by rw [ip_comm, ip_one_right]

theorem tr_one : tr one = 3 := by apply Complex.ext <;> simp [one, tr]

theorem ip_one_one : ip one one = 3 := by rw [ip_one_right, tr_one]

/-- The complex-linear extension of a real-linear endomorphism. -/
def mapC (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert) : JC →ₗ[ℂ] JC where
  toFun z := ⟨f z.re, f z.im⟩
  map_add' z w := by apply JC.ext <;> simp
  map_smul' c z := by apply JC.ext <;> simp

@[simp] theorem mapC_re (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (z : JC) :
    (mapC f z).re = f z.re := rfl
@[simp] theorem mapC_im (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (z : JC) :
    (mapC f z).im = f z.im := rfl

theorem mapC_of (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (x : Glennie.Albert) :
    mapC f (of x) = of (f x) := by apply JC.ext <;> simp

theorem mapC_conj (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (z : JC) :
    mapC f (conj z) = conj (mapC f z) := by apply JC.ext <;> simp

theorem mapC_mul (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
    (hf : ∀ x y, f (jordan x y) = jordan (f x) (f y)) (z w : JC) :
    mapC f (mul z w) = mul (mapC f z) (mapC f w) := by
  apply JC.ext <;> simp [hf]

theorem mapC_ip (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
    (hf : ∀ x y, inner (f x) (f y) = inner x y) (z w : JC) :
    ip (mapC f z) (mapC f w) = ip z w := by
  apply Complex.ext <;> simp [hf]

end JC

end

end ThirteenPlanes.AlbertGrading.Grading
