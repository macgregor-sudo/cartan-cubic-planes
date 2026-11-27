module

public import ThirteenPlanes.AlbertGrading.Recognition.Lines

@[expose] public section

/-!
# A frame contrast in `span{e, u_{±g}, u_{±h}}`, `g, h` independent

Comparing the coefficients of `u_{±g±h}` in `u ∘ u = σu` shows that the contrast lies in
`span{e, u_{±g}}` or in `span{e, u_{±h}}`. Used for recognition of systems with 52 positive shares, where the contrasts of the
two remaining frames of a quartet lie in the complexified product space of the other two.
-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

section Comb

variable {g h : Charge}

/-- The charge `a g + b h`. -/
def comb (g h : Charge) (a b : ZMod 3) : Charge := a • g + b • h

theorem comb_add (a b c d : ZMod 3) : comb g h a b + comb g h c d = comb g h (a + c) (b + d) := by
  simp only [comb, add_smul]; abel

theorem comb_neg (a b : ZMod 3) : -comb g h a b = comb g h (-a) (-b) := by
  simp only [comb, neg_smul, neg_add]

theorem comb_g : comb g h 1 0 = g := by simp [comb]
theorem comb_h : comb g h 0 1 = h := by simp [comb]

theorem comb_injective (hd : ¬ F3Dependent g h) {a b c d : ZMod 3}
    (he : comb g h a b = comb g h c d) : a = c ∧ b = d := by
  by_contra hne
  apply hd
  refine ⟨a - c, b - d, ?_, ?_⟩
  · by_contra h'
    push_neg at h'
    exact hne ⟨sub_eq_zero.mp h'.1, sub_eq_zero.mp h'.2⟩
  · have : comb g h a b - comb g h c d = 0 := by rw [he, sub_self]
    rw [← this]; simp only [comb, sub_smul]; abel

theorem coef_comb (hd : ¬ F3Dependent g h) (a b c d : ZMod 3) :
    coef (comb g h a b) (titsBasis (comb g h c d)) = if (a, b) = (c, d) then 1 else 0 := by
  rw [coef_titsBasis]
  by_cases he : (a, b) = (c, d)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp
  · rw [if_neg he, if_neg]
    intro e
    exact he (Prod.ext_iff.mpr (comb_injective hd e))

theorem indep_of_signs (hd : ¬ F3Dependent g h) (s t : ZMod 3) (hs : s ≠ 0) (ht : t ≠ 0) :
    ¬ F3Dependent (s • g) (t • h) := by
  rintro ⟨x, y, hxy, he⟩
  apply hd
  refine ⟨x * s, y * t, ?_, by rw [mul_smul, mul_smul]; exact he⟩
  rcases hxy with hx | hy
  · exact Or.inl (mul_ne_zero hx hs)
  · exact Or.inr (mul_ne_zero hy ht)

end Comb

/-- A frame contrast in `span{e, u_g, u_{-g}, u_h, u_{-h}}` with `g, h` independent lies in
`span{e, u_g, u_{-g}}` or in `span{e, u_h, u_{-h}}`. -/
theorem contrast_four {P : ZMod 3 → CompactTits} (hP : IsTitsFrame P) {g h : Charge}
    (hd : ¬ F3Dependent g h)
    (hu : titsContrast P ∈ Submodule.span ℂ
      {firstTitsOne, titsBasis g, titsBasis (-g), titsBasis h, titsBasis (-h)}) :
    titsContrast P ∈ Submodule.span ℂ {firstTitsOne, titsBasis g, titsBasis (-g)} ∨
      titsContrast P ∈ Submodule.span ℂ {firstTitsOne, titsBasis h, titsBasis (-h)} := by
  have hg0 : g ≠ 0 := by rintro rfl; exact hd ⟨1, 0, Or.inl one_ne_zero, by simp⟩
  have hh0 : h ≠ 0 := by rintro rfl; exact hd ⟨0, 1, Or.inr one_ne_zero, by simp⟩
  obtain ⟨e, z1, hz1, hu⟩ := Submodule.mem_span_insert.mp hu
  obtain ⟨α, z2, hz2, hz1⟩ := Submodule.mem_span_insert.mp hz1
  obtain ⟨β, z3, hz3, hz2⟩ := Submodule.mem_span_insert.mp hz2
  obtain ⟨γ, z4, hz4, hz3⟩ := Submodule.mem_span_insert.mp hz3
  obtain ⟨δ, rfl⟩ := Submodule.mem_span_singleton.mp hz4
  subst hz1 hz2 hz3
  have ht := contrast_trace hP
  rw [hu] at ht
  simp only [map_add, map_smul, tr1_one, tr1_titsBasis, if_neg hg0, if_neg (neg_ne_zero.mpr hg0),
    if_neg hh0, if_neg (neg_ne_zero.mpr hh0), smul_eq_mul, mul_zero, add_zero] at ht
  have he : e = 0 := by linear_combination ht / 3
  subst he
  rw [zero_smul, zero_add] at hu
  -- the four mixed products
  obtain ⟨c1, hc1, e1⟩ := titsBasis_indep g h hd
  obtain ⟨c2, hc2, e2⟩ := titsBasis_indep g (-h) (by
    simpa using indep_of_signs hd 1 (-1) one_ne_zero (by decide))
  obtain ⟨c3, hc3, e3⟩ := titsBasis_indep (-g) h (by
    simpa using indep_of_signs hd (-1) 1 (by decide) one_ne_zero)
  obtain ⟨c4, hc4, e4⟩ := titsBasis_indep (-g) (-h) (by
    simpa using indep_of_signs hd (-1) (-1) (by decide) (by decide))
  have e1' : firstTitsJordanProduct (titsBasis h) (titsBasis g) = c1 • titsBasis (g + h) := by
    rw [firstTitsJordanProduct_comm]; exact e1
  have e2' : firstTitsJordanProduct (titsBasis (-h)) (titsBasis g) = c2 • titsBasis (g + -h) := by
    rw [firstTitsJordanProduct_comm]; exact e2
  have e3' : firstTitsJordanProduct (titsBasis h) (titsBasis (-g)) = c3 • titsBasis (-g + h) := by
    rw [firstTitsJordanProduct_comm]; exact e3
  have e4' : firstTitsJordanProduct (titsBasis (-h)) (titsBasis (-g)) = c4 • titsBasis (-g + -h) := by
    rw [firstTitsJordanProduct_comm]; exact e4
  have h1 := contrast_square hP
  rw [hu] at h1
  simp only [← firstTitsJordanBilinear_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    at h1
  simp only [firstTitsJordanBilinear_apply, e1, e2, e3, e4, e1', e2', e3', e4',
    titsBasis_product_dependent _ _ (dep_self g), titsBasis_product_dependent _ _ (dep_neg g),
    titsBasis_product_dependent _ _ (dep_neg' g), titsBasis_product_dependent _ _ (dep_neg_neg g),
    titsBasis_product_dependent _ _ (dep_self h), titsBasis_product_dependent _ _ (dep_neg h),
    titsBasis_product_dependent _ _ (dep_neg' h), titsBasis_product_dependent _ _ (dep_neg_neg h),
    map_add, compactInvolution_complex_smul, titsBasis_involution, neg_neg] at h1
  have hadd : ∀ a b c d : ZMod 3, comb g h a b + comb g h c d = comb g h (a + c) (b + d) :=
    comb_add
  have hneg : ∀ a b : ZMod 3, -comb g h a b = comb g h (-a) (-b) := comb_neg
  have hcoef := coef_comb hd
  have hg' : g = comb g h 1 0 := comb_g.symm
  have hh' : h = comb g h 0 1 := comb_h.symm
  generalize comb g h = E at hadd hneg hcoef hg' hh'
  rw [hg', hh'] at h1
  simp only [hadd, hneg] at h1
  have k1 := congrArg (coef (E 1 1)) h1
  have k2 := congrArg (coef (E 1 (-1))) h1
  have k3 := congrArg (coef (E (-1) 1)) h1
  have k4 := congrArg (coef (E (-1) (-1))) h1
  simp only [map_add, map_smul, hcoef, smul_eq_mul] at k1 k2 k3 k4
  simp (config := { decide := true }) only [Prod.mk.injEq, ite_true, ite_false, if_true,
    if_false, mul_zero, mul_one, add_zero, zero_add] at k1 k2 k3 k4
  have hz (x c : ℂ) (hc : c ≠ 0) (k : x * (2 * c) = 0) : x = 0 := by
    rcases mul_eq_zero.mp k with h | h
    · exact h
    · exact absurd h (mul_ne_zero two_ne_zero hc)
  have hag : α * γ = 0 := hz _ c1 hc1 (by linear_combination k1)
  have had : α * δ = 0 := hz _ c2 hc2 (by linear_combination k2)
  have hbg : β * γ = 0 := hz _ c3 hc3 (by linear_combination k3)
  have hbd : β * δ = 0 := hz _ c4 hc4 (by linear_combination k4)
  have mem1 (x y : ℂ) : x • titsBasis g + y • titsBasis (-g) ∈
      Submodule.span ℂ {firstTitsOne, titsBasis g, titsBasis (-g)} :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have mem2 (x y : ℂ) : x • titsBasis h + y • titsBasis (-h) ∈
      Submodule.span ℂ {firstTitsOne, titsBasis h, titsBasis (-h)} :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  by_cases hα : α = 0
  · by_cases hβ : β = 0
    · right; convert mem2 γ δ using 1; rw [hu, hα, hβ]; simp
    · have hγ : γ = 0 := (mul_eq_zero.mp hbg).resolve_left hβ
      have hδ : δ = 0 := (mul_eq_zero.mp hbd).resolve_left hβ
      left; convert mem1 α β using 1; rw [hu, hγ, hδ]; simp [add_assoc]
  · have hγ : γ = 0 := (mul_eq_zero.mp hag).resolve_left hα
    have hδ : δ = 0 := (mul_eq_zero.mp had).resolve_left hα
    left; convert mem1 α β using 1; rw [hu, hγ, hδ]; simp [add_assoc]

end

end ThirteenPlanes.AlbertGrading
