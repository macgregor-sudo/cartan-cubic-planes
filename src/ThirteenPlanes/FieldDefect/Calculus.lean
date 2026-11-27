module

public import ThirteenPlanes.FieldDefect.Statements
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

/-! Calculus helpers for radial field defect: real derivatives of sums of real parts of triple products
of real-linear coordinate functions on `ℂ^m`, and the gradient length through `toDual`. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Defect

open Complex

variable {m : ℕ}

/-- The coordinate `z ↦ zᵢ`, real linear. -/
def pr (i : Fin m) : Field m →L[ℝ] ℂ :=
  (EuclideanSpace.proj i : Field m →L[ℂ] ℂ).restrictScalars ℝ

/-- The conjugate coordinate `z ↦ z̄ᵢ`, real linear. -/
def cpr (i : Fin m) : Field m →L[ℝ] ℂ :=
  conjCLE.toContinuousLinearMap.comp (pr i)

@[simp] lemma pr_apply (i : Fin m) (z : Field m) : pr i z = z i := rfl

@[simp] lemma cpr_apply (i : Fin m) (z : Field m) : cpr i z = (starRingEnd ℂ) (z i) := rfl

/-- A term `c · Re(L₁ x · L₂ x · L₃ x)`. -/
abbrev Term (m : ℕ) := ℝ × (Field m →L[ℝ] ℂ) × (Field m →L[ℝ] ℂ) × (Field m →L[ℝ] ℂ)

/-- Value of a list of terms. -/
def triSum (l : List (Term m)) (x : Field m) : ℝ :=
  (l.map fun e => e.1 * (e.2.1 x * e.2.2.1 x * e.2.2.2 x).re).sum

/-- The derivative of one term at `z`. -/
def termDeriv (e : Term m) (z : Field m) : Field m →L[ℝ] ℝ :=
  e.1 • reCLM.comp ((e.2.1 z * e.2.2.1 z) • e.2.2.2 +
    e.2.2.2 z • (e.2.1 z • e.2.2.1 + e.2.2.1 z • e.2.1))

/-- The derivative of a list of terms at `z`. -/
def triDeriv : List (Term m) → Field m → (Field m →L[ℝ] ℝ)
  | [], _ => 0
  | e :: l, z => termDeriv e z + triDeriv l z

lemma termDeriv_apply (e : Term m) (z v : Field m) :
    termDeriv e z v = e.1 * (e.2.1 v * e.2.2.1 z * e.2.2.2 z + e.2.1 z * e.2.2.1 v * e.2.2.2 z +
      e.2.1 z * e.2.2.1 z * e.2.2.2 v).re := by
  simp only [termDeriv, smul_apply, ContinuousLinearMap.comp_apply,
    add_apply, reCLM_apply, smul_eq_mul]
  congr 1
  congr 1
  ring

lemma triDeriv_apply (l : List (Term m)) (z v : Field m) :
    triDeriv l z v = (l.map fun e => e.1 * (e.2.1 v * e.2.2.1 z * e.2.2.2 z +
      e.2.1 z * e.2.2.1 v * e.2.2.2 z + e.2.1 z * e.2.2.1 z * e.2.2.2 v).re).sum := by
  induction l with
  | nil => simp [triDeriv]
  | cons e l ih =>
    simp only [triDeriv, add_apply, ih, termDeriv_apply, List.map_cons,
      List.sum_cons]

lemma hasFDerivAt_term (e : Term m) (z : Field m) :
    HasFDerivAt (fun x => e.1 * (e.2.1 x * e.2.2.1 x * e.2.2.2 x).re) (termDeriv e z) z := by
  have h1 := e.2.1.hasFDerivAt (x := z)
  have h2 := e.2.2.1.hasFDerivAt (x := z)
  have h3 := e.2.2.2.hasFDerivAt (x := z)
  have h := (reCLM.hasFDerivAt (x := e.2.1 z * e.2.2.1 z * e.2.2.2 z)).comp z
    ((h1.mul h2).mul h3)
  have h' := h.const_mul e.1
  exact h'

lemma hasFDerivAt_triSum (l : List (Term m)) (z : Field m) :
    HasFDerivAt (triSum l) (triDeriv l z) z := by
  induction l with
  | nil =>
    have hf : triSum ([] : List (Term m)) = fun _ => (0 : ℝ) := by funext x; simp [triSum]
    rw [hf]
    exact hasFDerivAt_const (0 : ℝ) z
  | cons e l ih =>
    have hf : triSum (e :: l) =
        fun x => e.1 * (e.2.1 x * e.2.2.1 x * e.2.2.2 x).re + triSum l x := by
      funext x; simp [triSum]
    rw [hf]
    exact (hasFDerivAt_term e z).add ih

lemma differentiable_triSum (l : List (Term m)) : Differentiable ℝ (triSum l) :=
  fun z => (hasFDerivAt_triSum l z).differentiableAt

/-- If the derivative at `z` is the real inner product with `g`, the gradient is `g`. -/
lemma gradient_eq_of_fderiv (W : Field m → ℝ) (z g : Field m)
    (h : ∀ v, fderiv ℝ W z v = (∑ i, (starRingEnd ℂ) (g i) * v i).re) : gradient W z = g := by
  have hd : fderiv ℝ W z = InnerProductSpace.toDual ℝ (Field m) g := by
    ext v
    rw [h v, InnerProductSpace.toDual_apply_apply]
    rw [PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inner, mul_comm]
  simp [gradient, hd]

/-- The squared Euclidean norm on `ℂ^m`. -/
lemma norm_sq_field (z : Field m) : ‖z‖ ^ 2 = ∑ i, normSq (z i) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Complex.sq_norm]

end ThirteenPlanes.AlbertGrading.Defect

end
