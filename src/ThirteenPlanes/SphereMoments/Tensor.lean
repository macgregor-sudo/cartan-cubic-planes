module

public import ThirteenPlanes.SphereMoments.Average
public import ThirteenPlanes.SphereMoments.Pairings

@[expose] public section

/-!
# Sphere averages of quadratic and quartic forms

Forms are given by coefficient arrays in a real orthonormal basis `e`.  We compute the averages of
quadratic and quartic forms, of products of two quadratic forms, and, for a symmetric trace-free
quartic array `T`, the averages of `T(x,x,x,x)`, `T(x,x,x,x) B(x,x)` and `T(x,x,x,x) S(x,x,x,x)`.
These are the moments used for the mean and variance of the field energy on the unit sphere.
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

/-- The quadratic form with coefficient array `B` in the basis `e`. -/
def quadraticForm (B : ι → ι → ℝ) (x : V) : ℝ :=
  ∑ a, ∑ b, B a b * (⟪e a, x⟫ * ⟪e b, x⟫)

/-- The quartic form with coefficient array `T` in the basis `e`. -/
def quarticForm (T : ι → ι → ι → ι → ℝ) (x : V) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (⟪e a, x⟫ * ⟪e b, x⟫ * ⟪e c, x⟫ * ⟪e d, x⟫)

section PiSums

theorem sum_pi_fin_two (F : (Fin 2 → ι) → ℝ) : ∑ i, F i = ∑ a, ∑ b, F ![a, b] := by
  simp only [sum_pi_fin_succ (n := 1), sum_pi_fin_succ (n := 0), Finset.univ_unique,
    Finset.sum_singleton]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => congrArg F ?_
  funext k; fin_cases k <;> rfl

theorem sum_pi_fin_four (F : (Fin 4 → ι) → ℝ) :
    ∑ i, F i = ∑ a, ∑ b, ∑ c, ∑ d, F ![a, b, c, d] := by
  simp only [sum_pi_fin_succ (n := 3), sum_pi_fin_succ (n := 2), sum_pi_fin_succ (n := 1),
    sum_pi_fin_succ (n := 0), Finset.univ_unique, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => congrArg F ?_
  funext k; fin_cases k <;> rfl

theorem sum_pi_fin_six (F : (Fin 6 → ι) → ℝ) :
    ∑ i, F i = ∑ a, ∑ b, ∑ c, ∑ d, ∑ f, ∑ g, F ![a, b, c, d, f, g] := by
  simp only [sum_pi_fin_succ (n := 5), sum_pi_fin_succ (n := 4), sum_pi_fin_succ (n := 3),
    sum_pi_fin_succ (n := 2), sum_pi_fin_succ (n := 1),
    sum_pi_fin_succ (n := 0), Finset.univ_unique, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => congrArg F ?_
  funext k; fin_cases k <;> rfl

theorem sum_pi_fin_eight (F : (Fin 8 → ι) → ℝ) :
    ∑ i, F i = ∑ a, ∑ b, ∑ c, ∑ d, ∑ f, ∑ g, ∑ h, ∑ l, F ![a, b, c, d, f, g, h, l] := by
  simp only [sum_pi_fin_succ (n := 7), sum_pi_fin_succ (n := 6), sum_pi_fin_succ (n := 5),
    sum_pi_fin_succ (n := 4), sum_pi_fin_succ (n := 3),
    sum_pi_fin_succ (n := 2), sum_pi_fin_succ (n := 1),
    sum_pi_fin_succ (n := 0), Finset.univ_unique, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ =>
    Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun l _ => congrArg F ?_
  funext k; fin_cases k <;> rfl

end PiSums

theorem quadraticForm_eq_pi (B : ι → ι → ℝ) (x : V) :
    quadraticForm e B x = ∑ i : Fin 2 → ι, B (i 0) (i 1) * ∏ k, ⟪e (i k), x⟫ := by
  rw [sum_pi_fin_two, quadraticForm]
  simp [Fin.prod_univ_two]

theorem quarticForm_eq_pi (T : ι → ι → ι → ι → ℝ) (x : V) :
    quarticForm e T x = ∑ i : Fin 4 → ι, T (i 0) (i 1) (i 2) (i 3) * ∏ k, ⟪e (i k), x⟫ := by
  rw [sum_pi_fin_four, quarticForm]
  simp [Fin.prod_univ_four]

theorem quarticForm_mul_quadraticForm_eq_pi (T : ι → ι → ι → ι → ℝ) (B : ι → ι → ℝ) (x : V) :
    quarticForm e T x * quadraticForm e B x =
      ∑ i : Fin 6 → ι, T (i 0) (i 1) (i 2) (i 3) * B (i 4) (i 5) * ∏ k, ⟪e (i k), x⟫ := by
  rw [sum_pi_fin_six, quarticForm, quadraticForm]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      simp [Fin.prod_univ_six]; ring

theorem quarticForm_mul_quarticForm_eq_pi (T S : ι → ι → ι → ι → ℝ) (x : V) :
    quarticForm e T x * quarticForm e S x =
      ∑ i : Fin 8 → ι, T (i 0) (i 1) (i 2) (i 3) * S (i 4) (i 5) (i 6) (i 7) *
        ∏ k, ⟪e (i k), x⟫ := by
  rw [sum_pi_fin_eight, quarticForm, quarticForm]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      simp [Fin.prod_univ_eight]; ring

theorem quadraticForm_mul_quadraticForm (B C : ι → ι → ℝ) (x : V) :
    quadraticForm e B x * quadraticForm e C x =
      quarticForm e (fun a b c d => B a b * C c d) x := by
  simp only [quadraticForm, quarticForm, Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable [Nontrivial V]

/-- Averages of coefficient-weighted products of basis coordinates. -/
theorem sphereAverage_sum_prod {p : ℕ} (c : (Fin p → ι) → ℝ) :
    sphereAverage (fun x => ∑ i : Fin p → ι, c i * ∏ k, ⟪e (i k), x⟫) =
      (∑ i : Fin p → ι, c i * wickSum p (fun k => e (i k))) / momentDenominator V (p / 2) := by
  rw [sphereAverage_sum _ fun i _ => by fun_prop, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sphereAverage_const_mul, sphereAverage_prod_inner, mul_div_assoc]

/-- The average of a quadratic form is its trace divided by `n`. -/
theorem sphereAverage_quadraticForm (B : ι → ι → ℝ) :
    sphereAverage (quadraticForm e B) = (∑ t, B t t) / Module.finrank ℝ V := by
  have h := sphereAverage_sum_prod e (p := 2) (fun i => B (i 0) (i 1))
  rw [sum_mul_wickSum_basis_two, show (2 : ℕ) / 2 = 1 by norm_num, momentDenominator_one] at h
  rw [show quadraticForm e B = fun x => _ from funext (quadraticForm_eq_pi e B), h]
  rfl

/-- The average of a quartic form is the sum of its three full contractions divided by
`n (n + 2)`. -/
theorem sphereAverage_quarticForm (T : ι → ι → ι → ι → ℝ) :
    sphereAverage (quarticForm e T) =
      (∑ w, ∑ t, (T t t w w + T t w t w + T t w w t)) /
        (Module.finrank ℝ V * (Module.finrank ℝ V + 2)) := by
  have h := sphereAverage_sum_prod e (p := 4) (fun i => T (i 0) (i 1) (i 2) (i 3))
  rw [sum_mul_wickSum_basis_four, show (4 : ℕ) / 2 = 2 by norm_num, momentDenominator_two] at h
  rw [show quarticForm e T = fun x => _ from funext (quarticForm_eq_pi e T), h]
  rfl

/-- The average of a product of two quadratic forms. -/
theorem sphereAverage_quadraticForm_mul (B C : ι → ι → ℝ) :
    sphereAverage (fun x => quadraticForm e B x * quadraticForm e C x) =
      (∑ w, ∑ t, (B t t * C w w + B t w * C t w + B t w * C w t)) /
        (Module.finrank ℝ V * (Module.finrank ℝ V + 2)) := by
  simp_rw [quadraticForm_mul_quadraticForm]
  exact sphereAverage_quarticForm e _

variable {T S : ι → ι → ι → ι → ℝ}

/-- A symmetric trace-free quartic form has average zero. -/
theorem sphereAverage_quarticForm_traceFree (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) :
    sphereAverage (quarticForm e T) = 0 := by
  rw [show quarticForm e T = fun x => _ from funext (quarticForm_eq_pi e T),
    sphereAverage_sum_prod, sum_wickSum_basis_four_traceFree e hT hT0, zero_div]

/-- A symmetric trace-free quartic form is orthogonal on the sphere to every quadratic form. -/
theorem sphereAverage_quarticForm_mul_quadraticForm (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T)
    (B : ι → ι → ℝ) :
    sphereAverage (fun x => quarticForm e T x * quadraticForm e B x) = 0 := by
  simp_rw [quarticForm_mul_quadraticForm_eq_pi]
  rw [sphereAverage_sum_prod, sum_wickSum_basis_six e hT hT0, zero_div]

/-- For `T` symmetric and trace-free and `S` symmetric, the average of `T(x⁴) S(x⁴)` over the unit
sphere is `24 ⟨T, S⟩ / (n (n + 2) (n + 4) (n + 6))`. -/
theorem sphereAverage_quarticForm_mul_quarticForm (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T)
    (hS : IsSymmetric4 S) :
    sphereAverage (fun x => quarticForm e T x * quarticForm e S x) =
      24 * (∑ a, ∑ b, ∑ c, ∑ d, T a b c d * S a b c d) /
        (Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) *
          (Module.finrank ℝ V + 6)) := by
  simp_rw [quarticForm_mul_quarticForm_eq_pi]
  rw [sphereAverage_sum_prod, sum_wickSum_basis_eight e hT hT0 hS,
    show (8 : ℕ) / 2 = 4 by norm_num, momentDenominator_four]

end

end ThirteenPlanes
