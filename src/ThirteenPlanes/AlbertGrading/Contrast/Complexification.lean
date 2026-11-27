module

public import Glennie.Native.AlgebraLaws
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Module

@[expose] public section

set_option backward.privateInPublic true

/-!
# The complexification of the native compact Albert algebra

`AlbertC` models `J_ℂ = J ⊗_ℝ ℂ` for `J = Glennie.Albert`: an element is a pair `(x, y)` read as
`x + i y`. The Jordan product and the trace pairing are extended complex-bilinearly, and `conj`
is the conjugation fixing `J`. This is the setting of Section 5 of the thirteen-planes paper.
-/

namespace ThirteenPlanes.AlbertGrading.Contrast

noncomputable section

/-- An element `re + i·im` of the complexified native Albert algebra. -/
@[ext] structure AlbertC where
  re : Glennie.Albert
  im : Glennie.Albert

namespace AlbertC

/-- The underlying pair. -/
def equivProd : AlbertC ≃ Glennie.Albert × Glennie.Albert where
  toFun x := (x.re, x.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup AlbertC := equivProd.addCommGroup

@[simp] theorem add_re (x y : AlbertC) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : AlbertC) : (x + y).im = x.im + y.im := rfl
@[simp] theorem zero_re : (0 : AlbertC).re = 0 := rfl
@[simp] theorem zero_im : (0 : AlbertC).im = 0 := rfl
@[simp] theorem neg_re (x : AlbertC) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : AlbertC) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : AlbertC) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : AlbertC) : (x - y).im = x.im - y.im := rfl

instance : SMul ℂ AlbertC :=
  ⟨fun z x => ⟨z.re • x.re - z.im • x.im, z.re • x.im + z.im • x.re⟩⟩

@[simp] theorem smul_re (z : ℂ) (x : AlbertC) : (z • x).re = z.re • x.re - z.im • x.im := rfl
@[simp] theorem smul_im (z : ℂ) (x : AlbertC) : (z • x).im = z.re • x.im + z.im • x.re := rfl

private theorem mul_smul' (z w : ℂ) (x : AlbertC) : (z * w) • x = z • w • x := by
  apply AlbertC.ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;> module

private theorem smul_add' (z : ℂ) (x y : AlbertC) : z • (x + y) = z • x + z • y := by
  apply AlbertC.ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module

private theorem add_smul' (z w : ℂ) (x : AlbertC) : (z + w) • x = z • x + w • x := by
  apply AlbertC.ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re, Complex.add_im] <;> module

instance : Module ℂ AlbertC where
  one_smul x := by apply AlbertC.ext <;> simp
  mul_smul := mul_smul'
  smul_zero z := by apply AlbertC.ext <;> simp
  smul_add := smul_add'
  add_smul := add_smul'
  zero_smul x := by apply AlbertC.ext <;> simp

theorem sum_re {ι : Type*} (s : Finset ι) (f : ι → AlbertC) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum (⟨⟨AlbertC.re, rfl⟩, fun _ _ => rfl⟩ : AlbertC →+ Glennie.Albert) f s

theorem sum_im {ι : Type*} (s : Finset ι) (f : ι → AlbertC) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum (⟨⟨AlbertC.im, rfl⟩, fun _ _ => rfl⟩ : AlbertC →+ Glennie.Albert) f s

/-- The real algebra inside its complexification. -/
def ofReal (x : Glennie.Albert) : AlbertC := ⟨x, 0⟩

/-- The conjugation of `J_ℂ` fixing `J`. -/
def conj (x : AlbertC) : AlbertC := ⟨x.re, -x.im⟩

/-- The complex-bilinear extension of the native Jordan product. -/
def jordan (x y : AlbertC) : AlbertC :=
  ⟨Glennie.jordan x.re y.re - Glennie.jordan x.im y.im,
    Glennie.jordan x.re y.im + Glennie.jordan x.im y.re⟩

/-- The complex-linear extension of the native trace. -/
def trace (x : AlbertC) : ℂ := ⟨Glennie.trace x.re, Glennie.trace x.im⟩

/-- The complex-bilinear extension `⟨x, y⟩ = tr (x ∘ y)` of the trace form. -/
def pair (x y : AlbertC) : ℂ := trace (jordan x y)

@[simp] theorem ofReal_re (x : Glennie.Albert) : (ofReal x).re = x := rfl
@[simp] theorem ofReal_im (x : Glennie.Albert) : (ofReal x).im = 0 := rfl
@[simp] theorem conj_re (x : AlbertC) : (conj x).re = x.re := rfl
@[simp] theorem conj_im (x : AlbertC) : (conj x).im = -x.im := rfl
@[simp] theorem jordan_re (x y : AlbertC) :
    (jordan x y).re = Glennie.jordan x.re y.re - Glennie.jordan x.im y.im := rfl
@[simp] theorem jordan_im (x y : AlbertC) :
    (jordan x y).im = Glennie.jordan x.re y.im + Glennie.jordan x.im y.re := rfl
@[simp] theorem trace_re (x : AlbertC) : (trace x).re = Glennie.trace x.re := rfl
@[simp] theorem trace_im (x : AlbertC) : (trace x).im = Glennie.trace x.im := rfl

theorem eq_ofReal_add_I_smul (x : AlbertC) : x = ofReal x.re + Complex.I • ofReal x.im := by
  apply AlbertC.ext <;> simp

@[simp] theorem ofReal_add (x y : Glennie.Albert) : ofReal (x + y) = ofReal x + ofReal y := by
  apply AlbertC.ext <;> simp

@[simp] theorem ofReal_zero : ofReal 0 = 0 := by apply AlbertC.ext <;> simp

@[simp] theorem ofReal_sub (x y : Glennie.Albert) : ofReal (x - y) = ofReal x - ofReal y := by
  apply AlbertC.ext <;> simp

@[simp] theorem ofReal_smul (r : ℝ) (x : Glennie.Albert) : ofReal (r • x) = (r : ℂ) • ofReal x := by
  apply AlbertC.ext <;> simp

theorem ofReal_injective : Function.Injective ofReal := fun _ _ h => congrArg AlbertC.re h

theorem ofReal_sum {ι : Type*} (s : Finset ι) (f : ι → Glennie.Albert) :
    ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ofReal (f i) :=
  map_sum (⟨⟨ofReal, ofReal_zero⟩, ofReal_add⟩ : Glennie.Albert →+ AlbertC) f s

@[simp] theorem conj_conj (x : AlbertC) : conj (conj x) = x := by apply AlbertC.ext <;> simp
@[simp] theorem conj_ofReal (x : Glennie.Albert) : conj (ofReal x) = ofReal x := by apply AlbertC.ext <;> simp
@[simp] theorem conj_add (x y : AlbertC) : conj (x + y) = conj x + conj y := by
  apply AlbertC.ext <;> simp [add_comm]
@[simp] theorem conj_zero : conj 0 = 0 := by apply AlbertC.ext <;> simp
@[simp] theorem conj_smul (z : ℂ) (x : AlbertC) : conj (z • x) = star z • conj x := by
  apply AlbertC.ext <;> simp <;> abel

theorem conj_sum {ι : Type*} (s : Finset ι) (f : ι → AlbertC) :
    conj (∑ i ∈ s, f i) = ∑ i ∈ s, conj (f i) :=
  map_sum (⟨⟨conj, conj_zero⟩, conj_add⟩ : AlbertC →+ AlbertC) f s

theorem conj_injective : Function.Injective conj := fun x y h => by
  simpa using congrArg conj h

theorem jordan_comm (x y : AlbertC) : jordan x y = jordan y x := by
  apply AlbertC.ext <;> simp [Glennie.jordan_comm] <;> abel

theorem jordan_add_left (x y z : AlbertC) : jordan (x + y) z = jordan x z + jordan y z := by
  apply AlbertC.ext <;> simp [Glennie.jordan_add_left] <;> abel

theorem jordan_add_right (x y z : AlbertC) : jordan x (y + z) = jordan x y + jordan x z := by
  rw [jordan_comm, jordan_add_left, jordan_comm y, jordan_comm z]

theorem jordan_smul_left (c : ℂ) (x y : AlbertC) : jordan (c • x) y = c • jordan x y := by
  apply AlbertC.ext <;> simp only [jordan_re, jordan_im, smul_re, smul_im, Glennie.jordan_add_left,
    Glennie.jordan_sub_left, Glennie.jordan_smul_left, Glennie.jordan_sub_right,
    Glennie.jordan_add_right] <;> module

theorem jordan_smul_right (c : ℂ) (x y : AlbertC) : jordan x (c • y) = c • jordan x y := by
  rw [jordan_comm, jordan_smul_left, jordan_comm]

/-- The product as a complex-bilinear map. -/
def jordanL : AlbertC →ₗ[ℂ] AlbertC →ₗ[ℂ] AlbertC :=
  LinearMap.mk₂ ℂ jordan jordan_add_left jordan_smul_left jordan_add_right jordan_smul_right

@[simp] theorem jordanL_apply (x y : AlbertC) : jordanL x y = jordan x y := rfl

theorem jordan_sum_left {ι : Type*} (s : Finset ι) (f : ι → AlbertC) (y : AlbertC) :
    jordan (∑ i ∈ s, f i) y = ∑ i ∈ s, jordan (f i) y := by
  simp only [← jordanL_apply, map_sum, LinearMap.sum_apply]

theorem jordan_sum_right {ι : Type*} (s : Finset ι) (x : AlbertC) (f : ι → AlbertC) :
    jordan x (∑ i ∈ s, f i) = ∑ i ∈ s, jordan x (f i) := by
  simp only [← jordanL_apply, map_sum]

@[simp] theorem jordan_ofReal (x y : Glennie.Albert) :
    jordan (ofReal x) (ofReal y) = ofReal (Glennie.jordan x y) := by
  apply AlbertC.ext <;> simp

@[simp] theorem jordan_one_left (x : AlbertC) : jordan (ofReal 1) x = x := by
  apply AlbertC.ext <;> simp

@[simp] theorem jordan_one_right (x : AlbertC) : jordan x (ofReal 1) = x := by
  rw [jordan_comm, jordan_one_left]

theorem conj_jordan (x y : AlbertC) : conj (jordan x y) = jordan (conj x) (conj y) := by
  apply AlbertC.ext <;> simp [Glennie.jordan_neg_left, Glennie.jordan_neg_right] <;> abel

theorem trace_add (x y : AlbertC) : trace (x + y) = trace x + trace y := by
  apply Complex.ext <;> simp [Glennie.trace_add]

theorem trace_smul (c : ℂ) (x : AlbertC) : trace (c • x) = c * trace x := by
  apply Complex.ext <;> simp [Glennie.trace_add, Glennie.trace_sub, Complex.mul_re,
    Complex.mul_im] <;> ring

theorem trace_zero : trace 0 = 0 := by
  apply Complex.ext <;> simp [Glennie.trace]

/-- The trace as a complex-linear map. -/
def traceL : AlbertC →ₗ[ℂ] ℂ where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

theorem trace_sum {ι : Type*} (s : Finset ι) (f : ι → AlbertC) :
    trace (∑ i ∈ s, f i) = ∑ i ∈ s, trace (f i) :=
  map_sum traceL f s

@[simp] theorem trace_ofReal (x : Glennie.Albert) : trace (ofReal x) = (Glennie.trace x : ℂ) := by
  apply Complex.ext <;> simp [Glennie.trace]

theorem trace_conj (x : AlbertC) : trace (conj x) = star (trace x) := by
  have h : Glennie.trace (-x.im) = -Glennie.trace x.im := by
    rw [show -x.im = (-1 : ℝ) • x.im by simp, Glennie.trace_smul]; ring
  apply Complex.ext <;> simp [h]

theorem pair_comm (x y : AlbertC) : pair x y = pair y x := by
  rw [pair, pair, jordan_comm]

@[simp] theorem pair_ofReal (x y : Glennie.Albert) :
    pair (ofReal x) (ofReal y) = (Glennie.inner x y : ℂ) := by
  simp [pair, Glennie.inner]

theorem pair_conj (x y : AlbertC) : pair (conj x) (conj y) = star (pair x y) := by
  rw [pair, pair, ← conj_jordan, trace_conj]

/-- The trace form as a complex-bilinear map. -/
def pairL : AlbertC →ₗ[ℂ] AlbertC →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ pair (fun x y z => by simp [pair, jordan_add_left, trace_add])
    (fun c x y => by simp [pair, jordan_smul_left, trace_smul])
    (fun x y z => by simp [pair, jordan_add_right, trace_add])
    (fun c x y => by simp [pair, jordan_smul_right, trace_smul])

@[simp] theorem pairL_apply (x y : AlbertC) : pairL x y = pair x y := rfl

end AlbertC

end

end ThirteenPlanes.AlbertGrading.Contrast
