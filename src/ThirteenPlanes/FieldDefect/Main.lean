module

public import ThirteenPlanes.FieldDefect.Seven
public import ThirteenPlanes.FieldDefect.Frames
public import ThirteenPlanes.FieldDefect.Minimizer

@[expose] public section

/-! Attainment and lower bounds for the defect, including the existence of a maximum on the unit sphere. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open Defect

/-- Radial field defect (i), from the count clause of the radial field classification. -/
theorem defectAttained (hcount : FieldClassification.FieldsCount) : Statements.DefectAttained :=
  Defect.defectAttained_of hcount

/-- Radial field defect (ii). -/
theorem defectSeven : Statements.DefectSeven := Defect.defectSeven

/-- Radial field defect (iii). -/
theorem sixFramesGap : Statements.SixFramesGap := Defect.sixFramesGap

/-- Radial field defect, all three parts. -/
theorem propDefect (hcount : FieldClassification.FieldsCount) :
    Statements.DefectAttained ∧ Statements.DefectSeven ∧ Statements.SixFramesGap :=
  ⟨defectAttained hcount, defectSeven, sixFramesGap⟩

/-- Non-vacuity: the unit sphere of `ℂ^m` is nonempty for `m ≥ 1`. -/
lemma Defect.sphere_nonempty (m : ℕ) (hm : 1 ≤ m) : (Metric.sphere (0 : Field m) 1).Nonempty := by
  let e : Field m := WithLp.toLp 2 fun i => if i = ⟨0, hm⟩ then 1 else 0
  refine ⟨e, ?_⟩
  rw [mem_sphere_zero_iff_norm]
  have h := norm_sq_field e
  have hs : ∑ i, Complex.normSq (e i) = 1 := by
    simp only [e]
    rw [Finset.sum_eq_single ⟨0, hm⟩]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rw [hs] at h
  have h0 : 0 ≤ ‖e‖ := norm_nonneg _
  nlinarith

/-- Junk-value check: for `m ≥ 1` every `W ∈ 𝒲_m` attains its defect at a point of the sphere,
and the defect bounds the integrand there; so `defect` is the manuscript's maximum. -/
theorem Defect.defect_isMax (m : ℕ) (hm : 1 ≤ m) (W : Field m → ℝ) (hW : W ∈ cubicClass m) :
    ∃ z ∈ Metric.sphere (0 : Field m) 1,
      |(1 / 9 : ℝ) * gradNorm W z ^ 2 - 1| = defect W ∧
      ∀ y ∈ Metric.sphere (0 : Field m) 1, |(1 / 9 : ℝ) * gradNorm W y ^ 2 - 1| ≤ defect W := by
  rw [cubicClass_eq_range] at hW
  obtain ⟨c, rfl⟩ := hW
  have hcont : ContinuousOn (fun z => integrand (c, z)) (Metric.sphere (0 : Field m) 1) :=
    (continuous_integrand.comp (continuous_const.prodMk continuous_id)).continuousOn
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_sphere (0 : Field m) 1).exists_isMaxOn (sphere_nonempty m hm) hcont
  have hval : defFun c = integrand (c, z) := by
    rw [defFun_eq]
    exact IsGreatest.csSup_eq ⟨⟨z, hz, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact isMaxOn_iff.mp hmax y hy⟩
  refine ⟨z, hz, ?_, fun y hy => ?_⟩
  · rw [gradNorm_eq]
    change integrand (c, z) = defFun c
    rw [hval]
  · rw [gradNorm_eq]
    change integrand (c, y) ≤ defFun c
    exact integrand_le c y hy

end ThirteenPlanes.AlbertGrading

end
