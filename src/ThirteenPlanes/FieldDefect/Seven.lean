module

public import ThirteenPlanes.FieldDefect.Calculus

@[expose] public section

/-! Radial field defect (ii): the cubic `W₄(z₁,…,z₄) + Re z₅³ + Re z₆³ + Re z₇³` lies in `𝒲₇` and has
defect exactly `3/4`; hence `δ₇ ≤ 3/4`.

Route: as printed. The real gradient is computed in closed form (Wirtinger form of each monomial),
`(1/9)‖∇W‖² = (∑_{p<4}|z_p|²)² + |z₄|⁴ + |z₅|⁴ + |z₆|⁴` is checked as a polynomial identity (this is
`‖∇W₄‖² = 9‖z'‖⁴` of the four-field model plus the three planes), and the four masses lie in the simplex. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Defect

open Complex

/-- `Re(∏ᵢ Lᵢ(vᵢ))` as a real trilinear form. -/
def triForm (L : Fin 3 → (ℂ →ₗ[ℝ] ℂ)) : TriForm :=
  reLm.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℝ (Fin 3) ℂ).compLinearMap L)

lemma triForm_apply (L : Fin 3 → (ℂ →ₗ[ℝ] ℂ)) (v : Fin 3 → ℂ) :
    triForm L v = (L 0 (v 0) * L 1 (v 1) * L 2 (v 2)).re := by
  simp [triForm, Fin.prod_univ_three]

/-- The real-linear conjugation. -/
def cj : ℂ →ₗ[ℝ] ℂ := conjAe.toLinearMap

@[simp] lemma cj_apply (a : ℂ) : cj a = (starRingEnd ℂ) a := rfl

/-- The four index triples of `W₄` inside `Fin 7`. -/
def tr : Fin 4 → Triple 7
  | 0 => ⟨![0, 1, 2], by decide⟩
  | 1 => ⟨![0, 1, 3], by decide⟩
  | 2 => ⟨![0, 2, 3], by decide⟩
  | 3 => ⟨![1, 2, 3], by decide⟩

/-- The four three-field terms of `W₄`: `−3Re(z₀z̄₁z₂)`, `−3Re(z₀z₁z̄₃)`, `−3Re(z₀z̄₂z₃)`,
`−3Re(z₁z₂z₃)`. -/
def form : Fin 4 → TriForm
  | 0 => (-3 : ℝ) • triForm ![LinearMap.id, cj, LinearMap.id]
  | 1 => (-3 : ℝ) • triForm ![LinearMap.id, LinearMap.id, cj]
  | 2 => (-3 : ℝ) • triForm ![LinearMap.id, cj, LinearMap.id]
  | 3 => (-3 : ℝ) • triForm ![LinearMap.id, LinearMap.id, LinearMap.id]

/-- The trilinear data of the seven-field cubic. -/
def sevenT (t : Triple 7) : TriForm := ∑ k : Fin 4, if t = tr k then form k else 0

lemma sevenCubic_eq_fieldCubic : sevenCubic = fieldCubic sevenT := by
  funext z
  have hs : ∑ t : Triple 7, sevenT t (fun a => z (t.1 a)) =
      ∑ k : Fin 4, form k (fun a => z ((tr k).1 a)) := by
    simp only [sevenT, sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∀ t : Triple 7, (if t = tr k then form k else 0) (fun a => z (t.1 a)) =
        if t = tr k then form k (fun a => z ((tr k).1 a)) else 0 := by
      intro t; split_ifs with h <;> simp [h]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [fieldCubic, hs]
  simp only [sevenCubic, W4, diagonalCubic, Fin.sum_univ_seven, Fin.sum_univ_four, form, tr,
    smul_apply, triForm_apply]
  simp [Complex.mul_re, Complex.mul_im, pow_succ]
  ring

lemma sevenCubic_mem : sevenCubic ∈ cubicClass 7 := ⟨sevenT, sevenCubic_eq_fieldCubic⟩

/-- The eleven triple-product terms of the seven-field cubic. -/
def l7 : List (Term 7) :=
  [(1, pr 0, pr 0, pr 0), (1, pr 1, pr 1, pr 1), (1, pr 2, pr 2, pr 2), (1, pr 3, pr 3, pr 3),
   (-3, pr 1, pr 2, pr 3), (-3, pr 0, cpr 1, pr 2), (-3, pr 0, cpr 2, pr 3), (-3, pr 0, cpr 3, pr 1),
   (1, pr 4, pr 4, pr 4), (1, pr 5, pr 5, pr 5), (1, pr 6, pr 6, pr 6)]

lemma sevenCubic_eq_triSum : sevenCubic = triSum l7 := by
  funext z
  simp only [sevenCubic, W4, triSum, l7, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, pr_apply, cpr_apply]
  simp [Complex.mul_re, Complex.mul_im, pow_succ]
  ring

/-- Conjugate gradient components `∂W/∂zᵢ + conj(∂W/∂z̄ᵢ)`. -/
def cg (z : Field 7) : Fin 7 → ℂ :=
  let c := starRingEnd ℂ
  ![3 * z 0 ^ 2 - 3 * (c (z 1) * z 2 + c (z 2) * z 3 + c (z 3) * z 1),
    3 * z 1 ^ 2 - 3 * z 2 * z 3 - 3 * z 0 * c (z 3) - 3 * c (z 0) * c (z 2),
    3 * z 2 ^ 2 - 3 * z 1 * z 3 - 3 * z 0 * c (z 1) - 3 * c (z 0) * c (z 3),
    3 * z 3 ^ 2 - 3 * z 1 * z 2 - 3 * z 0 * c (z 2) - 3 * c (z 0) * c (z 1),
    3 * z 4 ^ 2, 3 * z 5 ^ 2, 3 * z 6 ^ 2]

/-- The real gradient of the seven-field cubic. -/
def g7 (z : Field 7) : Field 7 := WithLp.toLp 2 (fun i => starRingEnd ℂ (cg z i))

lemma gradient_sevenCubic (z : Field 7) : gradient sevenCubic z = g7 z := by
  apply gradient_eq_of_fderiv
  intro v
  rw [sevenCubic_eq_triSum, (hasFDerivAt_triSum l7 z).fderiv, triDeriv_apply]
  simp only [g7, PiLp.toLp_apply, Complex.conj_conj, l7, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, pr_apply, cpr_apply, Fin.sum_univ_seven, cg]
  simp [Complex.mul_re, Complex.mul_im, pow_succ]
  ring

/-- `(1/9)‖∇W(z)‖² = (∑_{p<4}|z_p|²)² + |z₄|⁴ + |z₅|⁴ + |z₆|⁴`. -/
lemma gradNorm_sevenCubic_sq (z : Field 7) :
    (1 / 9 : ℝ) * gradNorm sevenCubic z ^ 2 =
      (normSq (z 0) + normSq (z 1) + normSq (z 2) + normSq (z 3)) ^ 2 +
        normSq (z 4) ^ 2 + normSq (z 5) ^ 2 + normSq (z 6) ^ 2 := by
  rw [gradNorm, gradient_sevenCubic, norm_sq_field]
  simp only [g7, PiLp.toLp_apply, Complex.normSq_conj, Fin.sum_univ_seven, cg]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_succ]
  ring

lemma sphere_sum (z : Field 7) (hz : z ∈ Metric.sphere (0 : Field 7) 1) :
    normSq (z 0) + normSq (z 1) + normSq (z 2) + normSq (z 3) + normSq (z 4) + normSq (z 5) +
      normSq (z 6) = 1 := by
  have h := norm_sq_field z
  rw [mem_sphere_zero_iff_norm.mp hz, Fin.sum_univ_seven] at h
  linarith

/-- The equal-mass point `(1/2,0,0,0,1/2,1/2,1/2)`. -/
def zStar : Field 7 := WithLp.toLp 2 ![1 / 2, 0, 0, 0, 1 / 2, 1 / 2, 1 / 2]

lemma zStar_mem : zStar ∈ Metric.sphere (0 : Field 7) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h := norm_sq_field zStar
  have hs : ∑ i, normSq (zStar i) = 1 := by
    simp only [zStar, PiLp.toLp_apply, Fin.sum_univ_seven]
    norm_num [Complex.normSq_apply]
  rw [hs] at h
  have h0 : 0 ≤ ‖zStar‖ := norm_nonneg _
  nlinarith

theorem defect_sevenCubic : defect sevenCubic = 3 / 4 := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨zStar, zStar_mem, ?_⟩
    simp only
    rw [gradNorm_sevenCubic_sq]
    simp only [zStar, PiLp.toLp_apply]
    norm_num [Complex.normSq_apply]
  · rintro _ ⟨z, hz, rfl⟩
    simp only
    rw [gradNorm_sevenCubic_sq]
    have hs := sphere_sum z hz
    have h0 := normSq_nonneg (z 0); have h1 := normSq_nonneg (z 1)
    have h2 := normSq_nonneg (z 2); have h3 := normSq_nonneg (z 3)
    have h4 := normSq_nonneg (z 4); have h5 := normSq_nonneg (z 5)
    have h6 := normSq_nonneg (z 6)
    set a := normSq (z 0) + normSq (z 1) + normSq (z 2) + normSq (z 3) with ha
    have ha0 : 0 ≤ a := by positivity
    have hup : a ^ 2 + normSq (z 4) ^ 2 + normSq (z 5) ^ 2 + normSq (z 6) ^ 2 ≤ 1 := by
      nlinarith
    have hlo : 1 / 4 ≤ a ^ 2 + normSq (z 4) ^ 2 + normSq (z 5) ^ 2 + normSq (z 6) ^ 2 := by
      nlinarith [sq_nonneg (a - normSq (z 4)), sq_nonneg (a - normSq (z 5)),
        sq_nonneg (a - normSq (z 6)), sq_nonneg (normSq (z 4) - normSq (z 5)),
        sq_nonneg (normSq (z 4) - normSq (z 6)), sq_nonneg (normSq (z 5) - normSq (z 6))]
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma defect_nonneg {m : ℕ} (W : Field m → ℝ) : 0 ≤ defect W := by
  apply Real.sSup_nonneg
  rintro _ ⟨z, _, rfl⟩
  exact abs_nonneg _

/-- Radial field defect (ii). -/
theorem defectSeven : Statements.DefectSeven := by
  refine ⟨sevenCubic_mem, defect_sevenCubic, ?_⟩
  rw [← defect_sevenCubic]
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨W, _, rfl⟩; exact defect_nonneg W⟩
  · exact ⟨sevenCubic, sevenCubic_mem, rfl⟩

end ThirteenPlanes.AlbertGrading.Defect

end
