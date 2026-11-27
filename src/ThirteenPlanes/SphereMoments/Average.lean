module

public import ThirteenPlanes.SphereMoments.Polar

@[expose] public section

/-!
# The uniform average over the unit sphere and its isotropic moments

`sphereAverage f` is the integral of `f` over the unit sphere of a finite-dimensional real
inner-product space against the normalized surface measure (surface measure induced from Lebesgue
measure, divided by its total mass).  The main result is the moment formula: the average of a
product of `2m` linear forms `⟪a k, x⟫` is the sum over perfect pairings of the products of inner
products, divided by `n (n + 2) ⋯ (n + 2m - 2)` with `n = dim V`; odd moments vanish.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The average of `f` over the unit sphere for the normalized surface measure. -/
def sphereAverage (f : V → ℝ) : ℝ :=
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  ((volume : Measure V).toSphere.real univ)⁻¹ * ∫ u, f u ∂(volume : Measure V).toSphere

/-- The normalization `n (n + 2) ⋯ (n + 2m - 2)` of the degree-`2m` moments, `n = dim V`. -/
def momentDenominator (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, ((Module.finrank ℝ V : ℝ) + 2 * j)

theorem momentDenominator_one : momentDenominator V 1 = Module.finrank ℝ V := by
  simp [momentDenominator]

theorem momentDenominator_two :
    momentDenominator V 2 = Module.finrank ℝ V * (Module.finrank ℝ V + 2) := by
  simp [momentDenominator, Finset.prod_range_succ]

theorem momentDenominator_three : momentDenominator V 3 =
    Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) := by
  simp only [momentDenominator, Finset.prod_range_succ, Finset.prod_range_zero]; push_cast; ring

theorem momentDenominator_four : momentDenominator V 4 =
    Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) *
      (Module.finrank ℝ V + 6) := by
  simp only [momentDenominator, Finset.prod_range_succ, Finset.prod_range_zero]; push_cast; ring

theorem momentDenominator_pos [Nontrivial V] (m : ℕ) : 0 < momentDenominator V m :=
  Finset.prod_pos fun j _ => by
    have : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
    positivity

section Borel

variable [MeasurableSpace V] [BorelSpace V]

theorem sphereAverage_eq (f : V → ℝ) :
    sphereAverage f =
      ((volume : Measure V).toSphere.real univ)⁻¹ * ∫ u, f u ∂(volume : Measure V).toSphere := by
  obtain rfl := BorelSpace.measurable_eq (α := V)
  rfl

theorem toSphere_real_univ_ne_zero [Nontrivial V] :
    (volume : Measure V).toSphere.real univ ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨Measure.measure_univ_ne_zero.2 (Measure.toSphere_ne_zero _), measure_ne_top _ _⟩

theorem integrable_toSphere_of_continuous {f : V → ℝ} (hf : Continuous f) :
    Integrable (fun u : Metric.sphere (0 : V) 1 => f u) (volume : Measure V).toSphere :=
  (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Borel

/-- The sphere average is additive on continuous functions. -/
theorem sphereAverage_add {f g : V → ℝ} (hf : Continuous f) (hg : Continuous g) :
    sphereAverage (fun x => f x + g x) = sphereAverage f + sphereAverage g := by
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  simp only [sphereAverage_eq]
  rw [integral_add (integrable_toSphere_of_continuous hf) (integrable_toSphere_of_continuous hg),
    mul_add]

/-- The sphere average is homogeneous. -/
theorem sphereAverage_const_mul (c : ℝ) (f : V → ℝ) :
    sphereAverage (fun x => c * f x) = c * sphereAverage f := by
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  simp only [sphereAverage_eq]
  rw [integral_const_mul]; ring

theorem sphereAverage_neg (f : V → ℝ) :
    sphereAverage (fun x => -f x) = -sphereAverage f := by
  simpa using sphereAverage_const_mul (-1) f

theorem sphereAverage_sub {f g : V → ℝ} (hf : Continuous f) (hg : Continuous g) :
    sphereAverage (fun x => f x - g x) = sphereAverage f - sphereAverage g := by
  simp only [sub_eq_add_neg]
  rw [sphereAverage_add (g := fun x => -g x) hf hg.neg, sphereAverage_neg]

/-- The sphere average commutes with finite sums of continuous functions. -/
theorem sphereAverage_sum {ι : Type*} (s : Finset ι) {f : ι → V → ℝ}
    (hf : ∀ i ∈ s, Continuous (f i)) :
    sphereAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, sphereAverage (f i) := by
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  simp only [sphereAverage_eq]
  rw [integral_finsetSum s fun i hi => integrable_toSphere_of_continuous (hf i hi),
    Finset.mul_sum]

/-- The average of a constant is that constant (in positive dimension). -/
theorem sphereAverage_const [Nontrivial V] (c : ℝ) : sphereAverage (fun _ : V => c) = c := by
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  have hZ := toSphere_real_univ_ne_zero (V := V)
  simp only [sphereAverage_eq, integral_const, smul_eq_mul]
  field_simp

/-- The variance of `f` over the unit sphere for the normalized surface measure. -/
def sphereVariance (f : V → ℝ) : ℝ :=
  sphereAverage (fun x => (f x - sphereAverage f) ^ 2)

/-- The sphere average depends only on the values on the unit sphere. -/
theorem sphereAverage_congr_sphere {f g : V → ℝ} (hfg : ∀ x : V, ‖x‖ = 1 → f x = g x) :
    sphereAverage f = sphereAverage g := by
  unfold sphereAverage
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact hfg u (by simpa using u.property)

/-- **Isotropic moments on the unit sphere.**  For `p` vectors `a k`, the average of
`∏ k, ⟪a k, x⟫` over the unit sphere is the pairing sum divided by `n (n+2) ⋯ (n + 2⌊p/2⌋ - 2)`;
for odd `p` the pairing sum, hence the average, is zero. -/
theorem sphereAverage_prod_inner [Nontrivial V] (p : ℕ) (a : Fin p → V) :
    sphereAverage (fun x => ∏ k, ⟪a k, x⟫) = wickSum p a / momentDenominator V (p / 2) := by
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  have hn0 : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hZ := toSphere_real_univ_ne_zero (V := V)
  set Z := (volume : Measure V).toSphere.real univ
  have hom : ∀ r : ℝ, 0 < r → ∀ x : V, (∏ k, ⟪a k, r • x⟫) = r ^ p * ∏ k, ⟪a k, x⟫ := by
    intro r _ x
    simp [inner_smul_right, Finset.prod_mul_distrib]
  have h1 := gaussIntegral_of_homogeneous (f := fun x => ∏ k, ⟪a k, x⟫) hom
  have h2 := gaussIntegral_prod p a
  rw [gaussIntegral_one] at h2
  rw [h1] at h2
  rw [sphereAverage_eq]
  set S := ∫ u, (∏ k, ⟪a k, (u : V)⟫) ∂(volume : Measure V).toSphere
  rcases Nat.even_or_odd' p with ⟨m, rfl | rfl⟩
  · rw [show 2 * m / 2 = m by omega] at h2 ⊢
    rw [radialMoment_add_two_mul] at h2
    have hR := radialMoment_pos (Module.finrank ℝ V - 1)
    have hcast : ((Module.finrank ℝ V - 1 : ℕ) : ℝ) + 1 = Module.finrank ℝ V := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    simp only [hcast] at h2
    have hprod : ∏ j ∈ Finset.range m, ((Module.finrank ℝ V : ℝ) + 2 * j) / 2 =
        momentDenominator V m / 2 ^ m := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, momentDenominator]
    rw [hprod] at h2
    have hD := momentDenominator_pos (V := V) m
    rw [eq_comm, ← sub_eq_zero] at h2
    field_simp at h2
    rw [one_div_pow] at h2
    field_simp at h2
    have h3 : wickSum (2 * m) a * Z - S * momentDenominator V m = 0 := by
      rcases mul_eq_zero.1 (h2.trans (mul_zero _)) with h | h
      · exact absurd h hR.ne'
      · exact h
    have hZ' : (volume : Measure V).toSphere.real univ ≠ 0 := hZ
    rw [eq_div_iff hD.ne', inv_mul_eq_div, div_mul_eq_mul_div, div_eq_iff hZ']
    linear_combination -h3
  · have hw : wickSum (2 * m + 1) a = 0 := wickSum_odd m a
    rw [hw, mul_zero, zero_mul] at h2
    have hR := radialMoment_pos (Module.finrank ℝ V - 1 + (2 * m + 1))
    have hS : S = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact h
      · exact absurd h hR.ne'
    rw [hS, hw]; simp

/-- Odd moments vanish. -/
theorem sphereAverage_prod_inner_odd [Nontrivial V] (m : ℕ) (a : Fin (2 * m + 1) → V) :
    sphereAverage (fun x => ∏ k, ⟪a k, x⟫) = 0 := by
  rw [sphereAverage_prod_inner, wickSum_odd, zero_div]

/-- Second moments: the average of `⟪a, x⟫ ⟪b, x⟫` is `⟪a, b⟫ / n`. -/
theorem sphereAverage_inner_mul_inner [Nontrivial V] (a b : V) :
    sphereAverage (fun x => ⟪a, x⟫ * ⟪b, x⟫) = ⟪a, b⟫ / Module.finrank ℝ V := by
  have h := sphereAverage_prod_inner 2 ![a, b]
  rw [show (2 : ℕ) / 2 = 1 by norm_num, momentDenominator_one] at h
  simp only [Fin.prod_univ_two, wickSum_two] at h
  simpa using h

/-- Fourth moments: the average of `⟪a,x⟫⟪b,x⟫⟪c,x⟫⟪d,x⟫` is
`(⟪a,b⟫⟪c,d⟫ + ⟪a,c⟫⟪b,d⟫ + ⟪a,d⟫⟪b,c⟫) / (n (n + 2))`. -/
theorem sphereAverage_inner_four [Nontrivial V] (a b c d : V) :
    sphereAverage (fun x => ⟪a, x⟫ * ⟪b, x⟫ * ⟪c, x⟫ * ⟪d, x⟫) =
      (⟪a, b⟫ * ⟪c, d⟫ + ⟪a, c⟫ * ⟪b, d⟫ + ⟪a, d⟫ * ⟪b, c⟫) /
        (Module.finrank ℝ V * (Module.finrank ℝ V + 2)) := by
  have h := sphereAverage_prod_inner 4 ![a, b, c, d]
  rw [show (4 : ℕ) / 2 = 2 by norm_num, momentDenominator_two] at h
  simp only [Fin.prod_univ_four, wickSum_four] at h
  simpa [mul_assoc] using h

/-- The average of an odd power of a linear form vanishes. -/
theorem sphereAverage_inner_odd [Nontrivial V] (a : V) :
    sphereAverage (fun x => ⟪a, x⟫) = 0 := by
  have h := sphereAverage_prod_inner_odd 0 ![a]
  simpa using h

end

end ThirteenPlanes
