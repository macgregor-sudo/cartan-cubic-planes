module

public import ThirteenPlanes.AlbertGrading.Contrast.BridgeTits
public import ThirteenPlanes.AlbertGrading.Grading.Statements
public import ThirteenPlanes.AlbertGrading.Recut.Shares
public import ThirteenPlanes.AlbertGrading.Completion.Statements

@[expose] public section

/-! Equivalences between the representations of the graded Albert algebra.

`Grading.JC` and `Contrast.AlbertC` both represent the complexification by pairs `x + i y`.
The equivalence preserves the real inclusion, conjugation, Jordan product, complex trace form
and frame contrasts. The first Tits model gives a third realization of the same algebra.

The centered spans `Recut.planeA` and `Contrast.framePlane` agree. The unbiasedness conditions
used in the frame models are all the overlap equality `inner (p a) (q b) = 1/3` for every outcome
pair. The planes of a `TightNativeCode` form an `IsThirteenPlaneSystem`. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Transport

open ThirteenPlanes.RoundCubics

/-! ## `Grading.JC ≃ Contrast.AlbertC` -/

/-- The identity on real and imaginary parts. -/
def complexEquiv : Grading.JC ≃ₗ[ℂ] Contrast.AlbertC where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  map_add' _ _ := by apply Contrast.AlbertC.ext <;> rfl
  map_smul' _ _ := by apply Contrast.AlbertC.ext <;> rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem complexEquiv_re (z : Grading.JC) : (complexEquiv z).re = z.re := rfl
@[simp] theorem complexEquiv_im (z : Grading.JC) : (complexEquiv z).im = z.im := rfl

theorem complexEquiv_of (x : Glennie.Albert) :
    complexEquiv (Grading.JC.of x) = Contrast.AlbertC.ofReal x := rfl

theorem complexEquiv_conj (z : Grading.JC) :
    complexEquiv (Grading.JC.conj z) = Contrast.AlbertC.conj (complexEquiv z) := rfl

theorem complexEquiv_one : complexEquiv Grading.JC.one = Contrast.AlbertC.ofReal 1 := rfl

theorem complexEquiv_mul (z w : Grading.JC) :
    complexEquiv (Grading.JC.mul z w) =
      Contrast.AlbertC.jordan (complexEquiv z) (complexEquiv w) := by
  apply Contrast.AlbertC.ext
  · rw [complexEquiv_re, Grading.JC.mul_re, Contrast.AlbertC.jordan_re]; rfl
  · rw [complexEquiv_im, Grading.JC.mul_im, Contrast.AlbertC.jordan_im]; rfl

theorem complexEquiv_ip (z w : Grading.JC) :
    Grading.JC.ip z w = Contrast.AlbertC.pair (complexEquiv z) (complexEquiv w) := by
  apply Complex.ext
  · rw [Grading.JC.ip_re, Contrast.AlbertC.pair, Contrast.AlbertC.trace_re,
      Contrast.AlbertC.jordan_re]
    change _ = Glennie.traceLinear _
    rw [map_sub]
    rfl
  · rw [Grading.JC.ip_im, Contrast.AlbertC.pair, Contrast.AlbertC.trace_im,
      Contrast.AlbertC.jordan_im]
    change _ = Glennie.traceLinear _
    rw [map_add]
    rfl

/-- Both complexifications give the same frame contrast `Σ_a ω^a p_a`. -/
theorem complexEquiv_contrast (p : Fin 3 → Glennie.Albert) :
    complexEquiv (Grading.contrast p) = Contrast.contrast p := by
  unfold Grading.contrast Contrast.contrast
  rw [map_sum]
  rfl

/-! ## Frame planes, unbiasedness, thirteen-plane systems -/

/-- Recut's plane of a frame in `J` is Contrast's `framePlane`. -/
theorem planeA_eq_framePlane {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    Recut.planeA p = Contrast.framePlane p :=
  (Contrast.framePlane_eq_native hp).symm

theorem contrast_unbiased_iff (p q : Fin 3 → Glennie.Albert) :
    Contrast.Unbiased p q ↔ NativeUnbiased p q := Contrast.unbiased_iff_inner p q

theorem nativeUnbiased_iff (p q : Fin 3 → Glennie.Albert) :
    NativeUnbiased p q ↔ ∀ a b, Glennie.inner (p a) (q b) = 1 / 3 := Iff.rfl

/-- The thirteen planes of a frame-level thirteen-plane system form a plane-level one. -/
theorem tightNativeCode_isThirteenPlaneSystem (c : TightNativeCode) :
    IsThirteenPlaneSystem (Set.range fun k => nativeFramePlane (c.point k)) :=
  ⟨fun k => nativeFramePlane (c.point k), rfl, c.decomposition.dimension, Recut.code_closed c,
    c.decomposition.pairwise_orthogonal⟩

end ThirteenPlanes.AlbertGrading.Transport
