module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

/-!
# Gaussian moments of products of linear forms

For a finite-dimensional real inner-product space `V` with its Lebesgue measure, we integrate
products of linear forms `x ↦ ∏ k, ⟪a k, x⟫` against the weight `exp (-‖x‖²)`.  Gaussian
integration by parts gives the Stein recursion, and induction gives the Wick (Isserlis) formula:
the integral is the sum over perfect pairings of the products of inner products, times `(1/2)^m`
times the total mass.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The sum over all perfect pairings of a family of vectors of the products of the paired
inner products (zero for an odd number of vectors). -/
def wickSum : (p : ℕ) → (Fin p → V) → ℝ
  | 0, _ => 1
  | 1, _ => 0
  | p + 2, a => ∑ k : Fin (p + 1), ⟪a 0, a k.succ⟫ * wickSum p (Fin.removeNth k (Fin.tail a))

@[simp] theorem wickSum_zero (a : Fin 0 → V) : wickSum 0 a = 1 := rfl

@[simp] theorem wickSum_one (a : Fin 1 → V) : wickSum 1 a = 0 := rfl

theorem wickSum_succ_succ (p : ℕ) (a : Fin (p + 2) → V) :
    wickSum (p + 2) a = ∑ k : Fin (p + 1), ⟪a 0, a k.succ⟫ *
      wickSum p (Fin.removeNth k (Fin.tail a)) := rfl

/-- The pairing sum of an odd family vanishes. -/
theorem wickSum_odd (m : ℕ) (a : Fin (2 * m + 1) → V) : wickSum (2 * m + 1) a = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show wickSum (2 * m + 1 + 2) a = 0
    rw [wickSum_succ_succ]
    simp [ih]

/-- The pairing sum of two vectors is their inner product. -/
theorem wickSum_two (a : Fin 2 → V) : wickSum 2 a = ⟪a 0, a 1⟫ := by
  simp [wickSum_succ_succ]

/-- The pairing sum of four vectors has three terms. -/
theorem wickSum_four (a : Fin 4 → V) :
    wickSum 4 a = ⟪a 0, a 1⟫ * ⟪a 2, a 3⟫ + ⟪a 0, a 2⟫ * ⟪a 1, a 3⟫ +
      ⟪a 0, a 3⟫ * ⟪a 1, a 2⟫ := by
  simp [wickSum_succ_succ, Fin.sum_univ_succ, Fin.removeNth, Fin.tail, Fin.succAbove]
  ring

/-- The Gaussian weight `exp (-‖x‖²)`. -/
def gaussWeight (x : V) : ℝ := Real.exp (-‖x‖ ^ 2)

theorem gaussWeight_pos (x : V) : 0 < gaussWeight x := Real.exp_pos _

theorem continuous_gaussWeight : Continuous (gaussWeight : V → ℝ) := by
  unfold gaussWeight; fun_prop

theorem prod_erase_eq_succAbove {M : Type*} [CommMonoid M] {p : ℕ} (k : Fin (p + 1))
    (f : Fin (p + 1) → M) : ∏ j ∈ Finset.univ.erase k, f j = ∏ j, f (k.succAbove j) := by
  rw [Fin.univ_succAbove _ k, Finset.erase_cons, Finset.prod_map]; rfl

theorem abs_prod_inner_le {ι : Type*} (s : Finset ι) (b : ι → V) (x : V) :
    |∏ j ∈ s, ⟪b j, x⟫| ≤ (∏ j ∈ s, ‖b j‖) * ‖x‖ ^ s.card := by
  rw [Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => abs_real_inner_le_norm _ _

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Integral against the Gaussian weight. -/
def gaussIntegral (f : V → ℝ) : ℝ := ∫ x, f x * gaussWeight x

variable [Nontrivial V]

theorem integrable_norm_pow_mul_gaussWeight (p : ℕ) :
    Integrable (fun x : V => ‖x‖ ^ p * gaussWeight x) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure V)
    (f := fun y : ℝ => y ^ p * Real.exp (-y ^ 2))).2 ?_
  · simpa [gaussWeight] using h
  have h0 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
    (s := ((Module.finrank ℝ V - 1 + p : ℕ) : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ V - 1 + p); linarith)
  refine h0.congr_fun (fun y hy => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, smul_eq_mul, pow_add, neg_mul, one_mul]
  ring

/-- A continuous function with a polynomial bound is integrable against the Gaussian weight. -/
theorem integrable_mul_gaussWeight {P : V → ℝ} (hP : Continuous P) (C : ℝ) (p : ℕ)
    (hb : ∀ x, |P x| ≤ C * ‖x‖ ^ p) : Integrable (fun x => P x * gaussWeight x) := by
  refine ((integrable_norm_pow_mul_gaussWeight p).const_mul C).mono'
    (hP.mul continuous_gaussWeight).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussWeight_pos x), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb x) (gaussWeight_pos x).le

theorem integrable_prod_inner_mul_gaussWeight {ι : Type*} (s : Finset ι) (b : ι → V) :
    Integrable (fun x => (∏ j ∈ s, ⟪b j, x⟫) * gaussWeight x) :=
  integrable_mul_gaussWeight (by fun_prop) _ s.card (abs_prod_inner_le s b)

/-- Gaussian integration by parts (Stein's identity) for a product of linear forms. -/
theorem gaussIntegral_inner_mul_prod {q : ℕ} (v : V) (b : Fin q → V) :
    gaussIntegral (fun x => ⟪v, x⟫ * ∏ k, ⟪b k, x⟫) =
      (1 / 2) * ∑ k, ⟪b k, v⟫ * gaussIntegral (fun x => ∏ j ∈ Finset.univ.erase k, ⟪b j, x⟫) := by
  classical
  let f : V → ℝ := fun x => ∏ k, ⟪b k, x⟫
  let f' : V → V →L[ℝ] ℝ := fun x =>
    ∑ k, (∏ j ∈ Finset.univ.erase k, ⟪b j, x⟫) • innerSL ℝ (b k)
  let g : V → ℝ := fun x => -(1 / 2) * gaussWeight x
  let g' : V → V →L[ℝ] ℝ := fun x => (-(1 / 2) * gaussWeight x) • (-(2 • innerSL ℝ x))
  have hf : ∀ x, HasFDerivAt f (f' x) x := fun x =>
    HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (innerSL ℝ (b k)).hasFDerivAt
  have hg : ∀ x, HasFDerivAt g (g' x) x := by
    intro x
    have h1 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.neg).exp
    have h2 := h1.const_mul (-(1 / 2 : ℝ))
    convert h2 using 1
    · ext x; simp [g, gaussWeight]
    · simp only [g', gaussWeight, smul_smul]; rfl
  have hg'v : ∀ x, g' x v = gaussWeight x * ⟪v, x⟫ := by
    intro x
    simp only [g', ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      innerSL_apply_apply, smul_eq_mul, real_inner_comm x v]
    norm_num; ring
  have hf'v : ∀ x, f' x v = ∑ k, (∏ j ∈ Finset.univ.erase k, ⟪b j, x⟫) * ⟪b k, v⟫ := by
    intro x
    simp [f', innerSL_apply_apply]
  have key := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure V)) (B := ContinuousLinearMap.mul ℝ ℝ) (v := v)
    (f := f) (f' := f') (g := g) (g' := g') ?_ ?_ ?_ (fun x _ => hf x) (fun x _ => hg x)
  rotate_left
  · simp only [ContinuousLinearMap.mul_apply', hf'v, g, Finset.sum_mul]
    exact integrable_finsetSum _ fun k _ =>
      ((integrable_prod_inner_mul_gaussWeight (Finset.univ.erase k) b).const_mul
        (⟪b k, v⟫ * (-(1 / 2)))).congr (Filter.Eventually.of_forall fun x => by ring)
  · simp only [ContinuousLinearMap.mul_apply', hg'v, f]
    have := integrable_mul_gaussWeight (P := fun x => (∏ k, ⟪b k, x⟫) * ⟪v, x⟫)
      (by fun_prop) ((∏ k, ‖b k‖) * ‖v‖) (q + 1) (fun x => by
        rw [abs_mul, pow_succ]
        have h1 := abs_prod_inner_le Finset.univ b x
        rw [Finset.card_univ, Fintype.card_fin] at h1
        calc _ ≤ ((∏ k, ‖b k‖) * ‖x‖ ^ q) * (‖v‖ * ‖x‖) :=
              mul_le_mul h1 (abs_real_inner_le_norm v x) (abs_nonneg _)
                (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity))
          _ = _ := by ring)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  · simp only [ContinuousLinearMap.mul_apply', f, g]
    refine ((integrable_prod_inner_mul_gaussWeight Finset.univ b).const_mul (-(1 / 2))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  simp only [ContinuousLinearMap.mul_apply', hg'v, hf'v, f, g] at key
  unfold gaussIntegral
  have lhs : ∫ x, (⟪v, x⟫ * ∏ k, ⟪b k, x⟫) * gaussWeight x =
      ∫ x, (∏ k, ⟪b k, x⟫) * (gaussWeight x * ⟪v, x⟫) := by
    congr 1; ext x; ring
  rw [lhs, key, Finset.mul_sum, ← integral_neg]
  have e2 : ∀ x, -((∑ k, (∏ j ∈ Finset.univ.erase k, ⟪b j, x⟫) * ⟪b k, v⟫) *
      (-(1 / 2) * gaussWeight x)) = ∑ k, 1 / 2 * ⟪b k, v⟫ *
        ((∏ j ∈ Finset.univ.erase k, ⟪b j, x⟫) * gaussWeight x) := by
    intro x
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [e2]
  rw [integral_finsetSum _ fun k _ => (integrable_prod_inner_mul_gaussWeight _ b).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

theorem gaussIntegral_inner (v : V) : gaussIntegral (fun x => ⟪v, x⟫) = 0 := by
  have h := gaussIntegral_inner_mul_prod (q := 0) v Fin.elim0
  simpa using h

/-- Stein's identity with the removed factor indexed through `succAbove`. -/
theorem gaussIntegral_prod_succ_succ {q : ℕ} (a : Fin (q + 2) → V) :
    gaussIntegral (fun x => ∏ k, ⟪a k, x⟫) =
      (1 / 2) * ∑ k : Fin (q + 1), ⟪a 0, a k.succ⟫ *
        gaussIntegral (fun x => ∏ j, ⟪Fin.removeNth k (Fin.tail a) j, x⟫) := by
  have h := gaussIntegral_inner_mul_prod (a 0) (Fin.tail a)
  simp only [prod_erase_eq_succAbove] at h
  have e : (fun x => ∏ k, ⟪a k, x⟫) = fun x => ⟪a 0, x⟫ * ∏ k, ⟪Fin.tail a k, x⟫ := by
    ext x; rw [Fin.prod_univ_succ]; rfl
  rw [e, h]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm]
  rfl

/-- **Wick's formula** for the Gaussian weight `exp (-‖x‖²)`: the integral of a product of `p`
linear forms is `(1/2)^(p/2)` times the pairing sum times the total mass (zero for odd `p`). -/
theorem gaussIntegral_prod : (p : ℕ) → (a : Fin p → V) →
    gaussIntegral (fun x => ∏ k, ⟪a k, x⟫) =
      (1 / 2) ^ (p / 2) * wickSum p a * gaussIntegral (fun _ : V => 1)
  | 0, a => by simp
  | 1, a => by
    have e : (fun x => ∏ k, ⟪a k, x⟫) = fun x => ⟪a 0, x⟫ := by ext x; simp
    rw [e, gaussIntegral_inner]; simp
  | p + 2, a => by
    rw [gaussIntegral_prod_succ_succ (q := p) a, wickSum_succ_succ,
      show (p + 2) / 2 = p / 2 + 1 by omega]
    simp_rw [gaussIntegral_prod p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

end

end ThirteenPlanes
