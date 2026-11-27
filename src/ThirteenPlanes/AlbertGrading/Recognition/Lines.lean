module

public import ThirteenPlanes.AlbertGrading.Recognition.Algebra

@[expose] public section

/-!
# A contrast in `span{e, u_g, u_{-g}}` lies on `ℂ u_g` or on `ℂ u_{-g}`

A frame equal as a set to the graded frame of `{±g}` has its contrast or conjugate contrast
on the line `ℂ u_g`.

-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem contrast_mem_of_coordinates {P : ZMod 3 → CompactTits} {S : Submodule ℂ (FirstTits ℂ)}
    (h : ∀ a, CompactTits.coordinates (P a) ∈ S) : titsContrast P ∈ S :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (h a)

theorem gradedCoords_mem (g : Charge) (b : ZMod 3) :
    gradedCoords g b ∈ Submodule.span ℂ {firstTitsOne, titsBasis g, titsBasis (-g)} := by
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem charge_neg_ne_zero {g : Charge} (hg : g ≠ 0) : -g ≠ 0 := neg_ne_zero.mpr hg

/-- A frame contrast in `span{e, u_g, u_{-g}}`, `g ≠ 0`, is a multiple of `u_g` or of `u_{-g}`. -/
theorem contrast_two {P : ZMod 3 → CompactTits} (hP : IsTitsFrame P) {g : Charge} (hg : g ≠ 0)
    (hu : titsContrast P ∈ Submodule.span ℂ {firstTitsOne, titsBasis g, titsBasis (-g)}) :
    ∃ l : ℂ, titsContrast P = l • titsBasis g ∨ titsContrast P = l • titsBasis (-g) := by
  obtain ⟨e, z, hz, hu⟩ := Submodule.mem_span_insert.mp hu
  obtain ⟨α, w, hw, hz⟩ := Submodule.mem_span_insert.mp hz
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have ht := contrast_trace hP
  rw [hu, hz] at ht
  simp only [map_add, map_smul, tr1_one, tr1_titsBasis, if_neg hg, if_neg (charge_neg_ne_zero hg),
    smul_eq_mul, mul_zero, add_zero] at ht
  have he : e = 0 := by linear_combination ht / 3
  subst he
  rw [zero_smul, zero_add] at hu
  have h1 := contrast_square hP
  rw [hu, hz] at h1
  have hc := congrArg (coef 0) h1
  have hgg : (0 : Charge) ≠ g + g := by rw [charge_add_self]; exact (charge_neg_ne_zero hg).symm
  have hgg' : (0 : Charge) ≠ -g + -g := by
    rw [charge_add_self, neg_neg]; exact Ne.symm hg
  simp only [← firstTitsJordanBilinear_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at hc
  simp only [firstTitsJordanBilinear_apply, map_add, map_smul, ite_true, if_true, titsBasis_product_dependent _ _ (dep_self g),
    titsBasis_product_dependent _ _ (dep_neg g), titsBasis_product_dependent _ _ (dep_neg' g),
    titsBasis_product_dependent _ _ (dep_neg_neg g), compactInvolution_complex_smul,
    titsBasis_involution, neg_neg, coef_titsBasis, if_neg hgg, if_neg hgg', add_neg_cancel,
    neg_add_cancel, if_pos rfl, if_neg (Ne.symm hg), if_neg (Ne.symm (charge_neg_ne_zero hg)),
    smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at hc
  have hab : α * β = 0 := by linear_combination hc / 2
  rcases mul_eq_zero.mp hab with h | h
  · subst h; exact ⟨β, Or.inr (by rw [hu, hz, zero_smul, zero_add])⟩
  · subst h; exact ⟨α, Or.inl (by rw [hu, hz, zero_smul, add_zero])⟩

/-- If a frame equals, as a set, the graded frame of `g ≠ 0`, its contrast or conjugate contrast is a
nonzero multiple of `u_g`. -/
theorem contrast_of_range {P : ZMod 3 → CompactTits} (hP : IsTitsFrame P) {g : Charge}
    (hg : g ≠ 0) (hr : Set.range P = Set.range (gradedFrame g)) :
    ∃ x ∈ ({titsContrast P, compactInvolution (titsContrast P)} : Set (FirstTits ℂ)),
      ∃ ζ : ℂ, ζ ≠ 0 ∧ x = ζ • titsBasis g := by
  have hmem : titsContrast P ∈ Submodule.span ℂ {firstTitsOne, titsBasis g, titsBasis (-g)} := by
    apply contrast_mem_of_coordinates
    intro a
    obtain ⟨b, hb⟩ : P a ∈ Set.range (gradedFrame g) := hr ▸ Set.mem_range_self a
    rw [← hb, gradedFrame_coordinates]
    exact gradedCoords_mem g b
  obtain ⟨l, hl | hl⟩ := contrast_two hP hg hmem
  · refine ⟨_, Or.inl rfl, l, ?_, hl⟩
    rintro rfl; exact contrast_ne_zero hP (by rw [hl, zero_smul])
  · refine ⟨_, Or.inr rfl, star l, ?_, ?_⟩
    · intro h; apply contrast_ne_zero hP; rw [hl, star_eq_zero.mp h, zero_smul]
    · rw [hl, compactInvolution_complex_smul, titsBasis_involution, neg_neg]

end

end ThirteenPlanes.AlbertGrading
