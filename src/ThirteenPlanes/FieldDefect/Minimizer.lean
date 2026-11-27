module

public import ThirteenPlanes.FieldDefect.Coefficients
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

/-! A strictly positive attained defect for disallowed field counts.

Euler's identity bounds `W²` on the unit sphere by `‖∇W‖²/9`. Homogeneity extends the bound to
all fields. Evaluating at the eight choices of entries `1,i` on each triple then bounds
every mixed coefficient and makes the relevant sublevel set compact. The field-count theorem
excludes a zero minimum when `m ≥ 1` and `m ∉ {1,4,13}`. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Defect

variable {m : ℕ}

lemma gradNorm_eq (W : Field m → ℝ) (z : Field m) : gradNorm W z = ‖fderiv ℝ W z‖ := by
  simp [gradNorm, gradient]

/-- `f(c) = def(W_c)`. -/
def defFun (c : Coef m) : ℝ := defect (coefCubic c)

/-- The integrand `|(1/9)‖∇W_c(z)‖² − 1|`. -/
def integrand (p : Coef m × Field m) : ℝ := |(1 / 9 : ℝ) * ‖fderiv ℝ (coefCubic p.1) p.2‖ ^ 2 - 1|

lemma continuous_integrand : Continuous (integrand (m := m)) := by
  unfold integrand
  exact continuous_abs.comp ((continuous_const.mul (continuous_fderiv_coefCubic.norm.pow 2)).sub
    continuous_const)

lemma defFun_eq (c : Coef m) :
    defFun c = sSup ((fun z => integrand (c, z)) '' Metric.sphere (0 : Field m) 1) := by
  simp only [defFun, defect, integrand, gradNorm_eq]

lemma continuous_defFun : Continuous (defFun (m := m)) := by
  have h := (isCompact_sphere (0 : Field m) 1).continuous_sSup
    (f := fun (c : Coef m) (z : Field m) => integrand (c, z)) continuous_integrand
  have he : defFun (m := m) = fun c => sSup ((fun z => integrand (c, z)) '' Metric.sphere 0 1) :=
    funext defFun_eq
  rw [he]
  exact h

lemma integrand_le (c : Coef m) (z : Field m) (hz : z ∈ Metric.sphere (0 : Field m) 1) :
    integrand (c, z) ≤ defFun c := by
  rw [defFun_eq]
  apply le_csSup
  · exact ((isCompact_sphere (0 : Field m) 1).image
      (continuous_integrand.comp (continuous_const.prodMk continuous_id))).bddAbove
  · exact ⟨z, hz, rfl⟩

lemma defFun_nonneg (c : Coef m) : 0 ≤ defFun c := by
  rw [defFun_eq]
  apply Real.sSup_nonneg
  rintro _ ⟨z, _, rfl⟩
  exact abs_nonneg _

lemma coefCubic_sq_le_sphere (c : Coef m) (B : ℝ) (hB : defFun c ≤ B) (z : Field m)
    (hz : z ∈ Metric.sphere (0 : Field m) 1) : coefCubic c z ^ 2 ≤ 1 + B := by
  have hi := (integrand_le c z hz).trans hB
  unfold integrand at hi
  have hG : ‖fderiv ℝ (coefCubic c) z‖ ^ 2 ≤ 9 * (1 + B) := by
    have := (le_abs_self _).trans hi
    linarith
  have he := euler (coefCubic c) ((contDiff_coefCubic c).differentiable one_ne_zero)
    (coefCubic_smul c) z
  have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hle : |fderiv ℝ (coefCubic c) z z| ≤ ‖fderiv ℝ (coefCubic c) z‖ := by
    have := (fderiv ℝ (coefCubic c) z).le_opNorm z
    rw [hn, mul_one, Real.norm_eq_abs] at this
    exact this
  rw [he] at hle
  have h0 : 0 ≤ |3 * coefCubic c z| := abs_nonneg _
  have hsq : (3 * coefCubic c z) ^ 2 ≤ ‖fderiv ℝ (coefCubic c) z‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ h0 hle 2
  nlinarith

lemma coefCubic_sq_le (c : Coef m) (B : ℝ) (hB : defFun c ≤ B) (y : Field m) :
    coefCubic c y ^ 2 ≤ ‖y‖ ^ 6 * (1 + B) := by
  by_cases hy : y = 0
  · have h0 : coefCubic c y = 0 := by
      have := coefCubic_smul c 0 y
      rw [zero_smul] at this
      rw [hy]; simpa using this
    rw [h0, hy]; simp
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set u := ‖y‖⁻¹ • y with hu
    have hus : u ∈ Metric.sphere (0 : Field m) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hyu : y = ‖y‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have h1 := coefCubic_sq_le_sphere c B hB u hus
    rw [hyu, coefCubic_smul, norm_smul, norm_norm, (mem_sphere_zero_iff_norm.mp hus), mul_one]
    have : (‖y‖ ^ 3 * coefCubic c u) ^ 2 = ‖y‖ ^ 6 * coefCubic c u ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The radius bounding every coefficient of a cubic with defect at most `B`. -/
def radius (m : ℕ) (B : ℝ) : ℝ :=
  ∑ t : Triple m, ∑ r : Fin 3 → Fin 2,
    (1 + ‖tPoint t r‖ ^ 6 * (1 + B) + |diagonalCubic (tPoint t r)|)

lemma coef_abs_le (c : Coef m) (B : ℝ) (hB0 : 0 ≤ B) (hB : defFun c ≤ B) (t : Triple m)
    (r : Fin 3 → Fin 2) : |c t r| ≤ radius m B := by
  have hterm : |c t r| ≤ 1 + ‖tPoint t r‖ ^ 6 * (1 + B) + |diagonalCubic (tPoint t r)| := by
    rw [coefCubic_tPoint c t r]
    have hsq := coefCubic_sq_le c B hB (tPoint t r)
    have ha : |coefCubic c (tPoint t r)| ≤ 1 + coefCubic c (tPoint t r) ^ 2 := by
      rcases le_total |coefCubic c (tPoint t r)| 1 with h | h
      · nlinarith [sq_nonneg (coefCubic c (tPoint t r))]
      · nlinarith [sq_abs (coefCubic c (tPoint t r)), abs_nonneg (coefCubic c (tPoint t r))]
    calc |coefCubic c (tPoint t r) - diagonalCubic (tPoint t r)|
        ≤ |coefCubic c (tPoint t r)| + |diagonalCubic (tPoint t r)| := abs_sub _ _
      _ ≤ _ := by linarith
  have hnn : ∀ (t' : Triple m) (r' : Fin 3 → Fin 2),
      0 ≤ 1 + ‖tPoint t' r'‖ ^ 6 * (1 + B) + |diagonalCubic (tPoint t' r')| := fun _ _ => by
    positivity
  refine hterm.trans ?_
  unfold radius
  calc 1 + ‖tPoint t r‖ ^ 6 * (1 + B) + |diagonalCubic (tPoint t r)|
      ≤ ∑ r' : Fin 3 → Fin 2, (1 + ‖tPoint t r'‖ ^ 6 * (1 + B) + |diagonalCubic (tPoint t r')|) :=
        Finset.single_le_sum (f := fun r' =>
          1 + ‖tPoint t r'‖ ^ 6 * (1 + B) + |diagonalCubic (tPoint t r')|)
          (fun r' _ => hnn t r') (Finset.mem_univ r)
    _ ≤ _ := Finset.single_le_sum (f := fun t' => ∑ r' : Fin 3 → Fin 2,
          (1 + ‖tPoint t' r'‖ ^ 6 * (1 + B) + |diagonalCubic (tPoint t' r')|))
          (fun t' _ => Finset.sum_nonneg fun r' _ => hnn t' r') (Finset.mem_univ t)

lemma norm_le_radius (c : Coef m) (B : ℝ) (hB0 : 0 ≤ B) (hB : defFun c ≤ B) :
    ‖c‖ ≤ radius m B := by
  have hR : 0 ≤ radius m B := by
    unfold radius
    exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun r _ => by positivity
  refine (pi_norm_le_iff_of_nonneg hR).mpr fun t => ?_
  refine (pi_norm_le_iff_of_nonneg hR).mpr fun r => ?_
  rw [Real.norm_eq_abs]
  exact coef_abs_le c B hB0 hB t r

/-- The derivative length of a cubic with zero defect is `3‖y‖²`. -/
lemma gradNorm_of_defFun_zero (c : Coef m) (h0 : defFun c = 0) (y : Field m) :
    gradNorm (coefCubic c) y = 3 * ‖y‖ ^ 2 := by
  have hdiff := (contDiff_coefCubic c).differentiable one_ne_zero
  have hsph : ∀ u ∈ Metric.sphere (0 : Field m) 1, ‖fderiv ℝ (coefCubic c) u‖ = 3 := by
    intro u hu
    have hi := integrand_le c u hu
    rw [h0] at hi
    unfold integrand at hi
    have he : (1 / 9 : ℝ) * ‖fderiv ℝ (coefCubic c) u‖ ^ 2 - 1 = 0 := abs_nonpos_iff.mp hi
    have hs : ‖fderiv ℝ (coefCubic c) u‖ ^ 2 = 3 ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) (by norm_num)).mp hs
  rw [gradNorm_eq]
  by_cases hy : y = 0
  · have h2 := fderiv_smul_hom (coefCubic c) hdiff (coefCubic_smul c) 2 two_ne_zero (0 : Field m)
    rw [smul_zero] at h2
    have hz : fderiv ℝ (coefCubic c) 0 = 0 := by
      have : (1 - (2 : ℝ) ^ 2) • fderiv ℝ (coefCubic c) 0 = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · norm_num at h
      · exact h
    rw [hy, hz]; simp
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set u := ‖y‖⁻¹ • y with hu
    have hus : u ∈ Metric.sphere (0 : Field m) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hyu : y = ‖y‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [hyu, fderiv_smul_hom (coefCubic c) hdiff (coefCubic_smul c) ‖y‖ hn.ne' u, norm_smul,
      hsph u hus, norm_smul, norm_norm, (mem_sphere_zero_iff_norm.mp hus), mul_one, norm_pow,
      norm_norm]
    ring

/-- Radial field defect (i), from the count clause of the radial field classification. -/
theorem defectAttained_of (hcount : FieldClassification.FieldsCount) : Statements.DefectAttained := by
  intro m hm h1 h4 h13
  set B := defFun (0 : Coef m) with hBdef
  have hB0 : 0 ≤ B := defFun_nonneg 0
  set K : Set (Coef m) := {c | defFun c ≤ B} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_le continuous_defFun continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Coef m)) (r := radius m B)).subset ?_
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_radius c B hB0 hc
  obtain ⟨cs, hcs, hmin⟩ := hKc.exists_isMinOn ⟨0, le_refl B⟩ continuous_defFun.continuousOn
  have hmin' : ∀ c : Coef m, defFun cs ≤ defFun c := by
    intro c
    by_cases hc : c ∈ K
    · exact isMinOn_iff.mp hmin c hc
    · have : B < defFun c := lt_of_not_ge hc
      exact (show defFun cs ≤ B from hcs).trans this.le
  have hdelta : delta m = defFun cs := by
    rw [delta, cubicClass_eq_range]
    apply IsLeast.csInf_eq
    refine ⟨⟨coefCubic cs, ⟨cs, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨W, ⟨c, rfl⟩, rfl⟩
    exact hmin' c
  refine ⟨⟨coefCubic cs, cubicClass_eq_range ▸ ⟨cs, rfl⟩, hdelta.symm⟩, ?_⟩
  rw [hdelta]
  rcases (defFun_nonneg cs).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hmem : coefCubic cs ∈ cubicClass m := cubicClass_eq_range ▸ ⟨cs, rfl⟩
    rcases hcount m hm (coefCubic cs) hmem
        ⟨fun r => 3 * r ^ 2, gradNorm_of_defFun_zero cs hzero.symm⟩ with h | h | h
    · exact h1 h
    · exact h4 h
    · exact h13 h

end ThirteenPlanes.AlbertGrading.Defect

end
