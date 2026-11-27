module

public import ThirteenPlanes.AlbertGrading.Grading.GradedPlanes

@[expose] public section

/-! # ternary grading theorem (iv): product spaces and shares of the graded planes -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC ThirteenPlanes.RoundCubics ThirteenPlanes.Graded

noncomputable section

variable {ρ : TernaryAction}

theorem of_re_eq (z : JC) : of z.re = (1 / 2 : ℂ) • (z + conj z) := by
  apply JC.ext
  · simp only [of_re, smul_re, add_re, conj_re, add_im, conj_im]
    norm_num
    module
  · simp only [of_im, smul_im, add_im, conj_im, add_re, conj_re]
    norm_num

/-- The real part of an element of `A_k ⊕ A_{-k}` lies in the graded plane. -/
theorem re_mem_gradedPlaneJ {k : Charge} {z : JC} (hz : z ∈ charSpace ρ k ⊔ charSpace ρ (-k)) :
    z.re ∈ gradedPlaneJ ρ k := by
  rw [mem_gradedPlaneJ_iff, of_re_eq]
  apply Submodule.smul_mem
  refine Submodule.add_mem _ hz ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  rw [conj_add, add_comm]
  exact Submodule.add_mem_sup (by rw [← neg_neg k]; exact conj_mem_charSpace hb)
    (conj_mem_charSpace ha)

/-- Products of two graded planes of independent grades. -/
theorem jordan_mem_of_independent (hρ : IsTernaryGrading ρ) {g h : Charge} {x y : Glennie.Albert}
    (hx : x ∈ gradedPlaneJ ρ g) (hy : y ∈ gradedPlaneJ ρ h) :
    Glennie.jordan x y ∈ gradedPlaneJ ρ (g + h) ⊔ gradedPlaneJ ρ (g - h) := by
  obtain ⟨a, ha, a', ha', hxa⟩ := Submodule.mem_sup.mp ((mem_gradedPlaneJ_iff _ _).mp hx)
  obtain ⟨b, hb, b', hb', hyb⟩ := Submodule.mem_sup.mp ((mem_gradedPlaneJ_iff _ _).mp hy)
  set S₁ := mul a b + mul a' b'
  set S₂ := mul a b' + mul a' b
  have hS₁ : S₁ ∈ charSpace ρ (g + h) ⊔ charSpace ρ (-(g + h)) := by
    refine Submodule.add_mem_sup (mul_mem_charSpace hρ ha hb) ?_
    have := mul_mem_charSpace hρ ha' hb'
    rwa [← neg_add] at this
  have hS₂ : S₂ ∈ charSpace ρ (g - h) ⊔ charSpace ρ (-(g - h)) := by
    refine Submodule.add_mem_sup ?_ ?_
    · have := mul_mem_charSpace hρ ha hb'
      rwa [← sub_eq_add_neg] at this
    · have := mul_mem_charSpace hρ ha' hb
      rwa [neg_sub, sub_eq_neg_add]
  have e : of (Glennie.jordan x y) = S₁ + S₂ := by
    rw [← of_mul, ← hxa, ← hyb, mul_add_left, mul_add_right, mul_add_right]
    simp only [S₁, S₂]; abel
  have e' : Glennie.jordan x y = S₁.re + S₂.re := by
    have := congrArg JC.re e
    simpa using this
  rw [e']
  exact Submodule.add_mem_sup (re_mem_gradedPlaneJ hS₁) (re_mem_gradedPlaneJ hS₂)

/-- Products within one graded plane. -/
theorem jordan_mem_of_same (hρ : IsTernaryGrading ρ) {g : Charge} {x y : Glennie.Albert}
    (hx : x ∈ gradedPlaneJ ρ g) (hy : y ∈ gradedPlaneJ ρ g) :
    Glennie.jordan x y ∈ (ℝ ∙ (1 : Glennie.Albert)) ⊔ gradedPlaneJ ρ g := by
  have h := jordan_mem_of_independent hρ hx hy
  rw [sub_self, charge_add_self, gradedPlaneJ_neg, sup_comm] at h
  obtain ⟨A, hA, B, hB, hAB⟩ := Submodule.mem_sup.mp h
  rw [← hAB]
  refine Submodule.add_mem_sup ?_ hB
  have hA' := (mem_gradedPlaneJ_iff _ _).mp hA
  rw [neg_zero, sup_idem, charSpace_zero_eq hρ] at hA'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hA'
  have : A = c.re • (1 : Glennie.Albert) := by
    have := congrArg JC.re hc
    simp [one] at this
    exact this.symm
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- A traceless sum of two graded-plane elements lies in the sum of the planes in `V`. -/
theorem mem_gradedPlane_sup (hρ : IsTernaryGrading ρ) {k₁ k₂ : Charge} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0)
    (v : NativeTraceless) (hv : (v : Glennie.Albert) ∈ gradedPlaneJ ρ k₁ ⊔ gradedPlaneJ ρ k₂) :
    v ∈ gradedPlane ρ k₁ ⊔ gradedPlane ρ k₂ := by
  obtain ⟨A, hA, B, hB, hAB⟩ := Submodule.mem_sup.mp hv
  have hA0 : A ∈ Glennie.traceLinear.ker := gradedPlaneJ_le_ker hρ h₁ hA
  have hB0 : B ∈ Glennie.traceLinear.ker := gradedPlaneJ_le_ker hρ h₂ hB
  have : v = ⟨A, hA0⟩ + ⟨B, hB0⟩ := Subtype.ext (by rw [← hAB]; rfl)
  rw [this]
  exact Submodule.add_mem_sup hA hB

theorem charge_add_ne_zero_of_points {p q : SignedPlaneIndex} :
    p.val.val + q.val.val ≠ 0 := rep_add_ne_zero

/-- The product space of two points lies in the planes of `g + h` and `g - h`. -/
theorem mixed_le (hρ : IsTernaryGrading ρ) {p q : SignedPlaneIndex} (hpq : p ≠ q) :
    mixedProductSpace nativeEqualCubic (pointPlane ρ p) (pointPlane ρ q) ≤
      gradedPlane ρ (p.val.val + q.val.val) ⊔ gradedPlane ρ (p.val.val - q.val.val) := by
  rw [mixedProductSpace_eq_span]
  apply Submodule.map₂_le.mpr
  intro x hx y hy
  apply mem_gradedPlane_sup hρ rep_add_ne_zero (rep_sub_ne_zero hpq)
  have horth : Glennie.inner (x : Glennie.Albert) y = 0 :=
    inner_eq_zero_of_gradedPlaneJ hρ rep_add_ne_zero (rep_sub_ne_zero hpq) hx hy
  have e : ((nativeEqualCubic.L x y : NativeTraceless) : Glennie.Albert) =
      Glennie.jordan x y := by
    change Glennie.traceless (Glennie.jordan x y) = _
    rw [Glennie.traceless]
    change _ - (Glennie.inner (x : Glennie.Albert) y / 3) • _ = _
    rw [horth, zero_div, zero_smul, sub_zero]
  rw [e]
  exact jordan_mem_of_independent hρ hx hy

theorem sup_finrank_four (hρ : IsTernaryGrading ρ) {k₁ k₂ : Charge} (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0)
    (e₁ : k₁ + k₂ ≠ 0) (e₂ : k₁ - k₂ ≠ 0) :
    Module.finrank ℝ ↥(gradedPlane ρ k₁ ⊔ gradedPlane ρ k₂) = 4 := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (gradedPlane ρ k₁) (gradedPlane ρ k₂)
  rw [(gradedPlane_orthogonal hρ e₁ e₂).disjoint.eq_bot, finrank_bot, add_zero,
    gradedPlane_finrank hρ h₁, gradedPlane_finrank hρ h₂] at hd
  exact hd

theorem two_ne_zero_charge {g : Charge} (hg : g ≠ 0) : g + g ≠ 0 := charge_add_self_ne_zero hg

/-- The product space of two distinct points is the sum of the planes of `g ± h`. -/
theorem mixed_eq (hρ : IsTernaryGrading ρ) {p q : SignedPlaneIndex} (hpq : p ≠ q) :
    mixedProductSpace nativeEqualCubic (pointPlane ρ p) (pointPlane ρ q) =
      gradedPlane ρ (p.val.val + q.val.val) ⊔ gradedPlane ρ (p.val.val - q.val.val) := by
  set g := p.val.val
  set h := q.val.val
  have e₁ : (g + h) + (g - h) ≠ 0 := by
    rw [show (g + h) + (g - h) = g + g by abel]; exact charge_add_self_ne_zero (rep_ne_zero p)
  have e₂ : (g + h) - (g - h) ≠ 0 := by
    rw [show (g + h) - (g - h) = h + h by abel]; exact charge_add_self_ne_zero (rep_ne_zero q)
  apply Submodule.eq_of_le_of_finrank_eq (mixed_le hρ hpq)
  rw [sup_finrank_four hρ rep_add_ne_zero (rep_sub_ne_zero hpq) e₁ e₂]
  exact mixedProductSpace_finrank (Graded.nativeRound) (pointPlane_orthogonal hρ hpq)
    (gradedPlane_closed hρ (rep_ne_zero p)) (gradedPlane_closed hρ (rep_ne_zero q))
    (pointPlane_finrank hρ p) (pointPlane_finrank hρ q)

/-! ## Collinearity in terms of representatives -/

theorem signedGrade_val (q : SignedPlaneIndex) (b : Bool) :
    (signedGrade q b).val = q.val.val ∨ (signedGrade q b).val = -q.val.val := by
  cases b
  · left; rfl
  · right; rfl

/-- The third point of a collinear triple has representative `±(g ± h)`. -/
theorem rep_of_collinear {p q r : SignedPlaneIndex} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h : signedCollinear p q r) :
    r.val.val = p.val.val + q.val.val ∨ r.val.val = -(p.val.val + q.val.val) ∨
      r.val.val = p.val.val - q.val.val ∨ r.val.val = -(p.val.val - q.val.val) := by
  obtain ⟨s, hs, -⟩ := (signedCollinear_iff_unique_completion p q r hpq hpr hqr).mp h
  unfold signedCompletesZero at hs
  rcases signedGrade_val q s.1 with h1 | h1 <;> rcases signedGrade_val r s.2 with h2 | h2 <;>
    rw [h1, h2] at hs
  · right; left; linear_combination hs
  · left; linear_combination -hs
  · right; right; right; linear_combination hs
  · right; right; left; linear_combination -hs

theorem collinear_of_rep {p q r : SignedPlaneIndex} (hpq : p ≠ q)
    (h : r.val.val = p.val.val + q.val.val ∨ r.val.val = -(p.val.val + q.val.val) ∨
      r.val.val = p.val.val - q.val.val ∨ r.val.val = -(p.val.val - q.val.val)) :
    signedCollinear p q r := by
  obtain ⟨l, ⟨hp, hq⟩, -⟩ := unique_joining_line p q hpq
  refine ⟨l, hp, hq, ?_⟩
  unfold signedPointOnLine at *
  rcases h with h | h | h | h <;> rw [h]
  · rw [chargeDot_add_right, hp, hq, add_zero]
  · rw [chargeDot_neg_right, chargeDot_add_right, hp, hq, add_zero, neg_zero]
  · rw [sub_eq_add_neg, chargeDot_add_right, chargeDot_neg_right, hp, hq, neg_zero, add_zero]
  · rw [chargeDot_neg_right, sub_eq_add_neg, chargeDot_add_right, chargeDot_neg_right, hp, hq,
      neg_zero, add_zero, neg_zero]

theorem pointPlane_of_rep (r : SignedPlaneIndex) {k : Charge}
    (h : r.val.val = k ∨ r.val.val = -k) : pointPlane ρ r = gradedPlane ρ k := by
  rcases h with h | h
  · unfold pointPlane; rw [h]
  · unfold pointPlane; rw [h, gradedPlane_neg]

/-- Ternary grading theorem (iv), product spaces. -/
theorem graded_mixed (hρ : IsTernaryGrading ρ) (p q r r' : SignedPlaneIndex) (hpq : p ≠ q)
    (hrr : r ≠ r') (hrp : r ≠ p) (hrq : r ≠ q) (hr'p : r' ≠ p) (hr'q : r' ≠ q)
    (hr : signedCollinear p q r) (hr' : signedCollinear p q r') :
    mixedProductSpace nativeEqualCubic (pointPlane ρ p) (pointPlane ρ q) =
      pointPlane ρ r ⊔ pointPlane ρ r' := by
  rw [mixed_eq hρ hpq]
  set k₁ := p.val.val + q.val.val
  set k₂ := p.val.val - q.val.val
  have A : (r.val.val = k₁ ∨ r.val.val = -k₁) ∨ (r.val.val = k₂ ∨ r.val.val = -k₂) := by
    rcases rep_of_collinear hpq (Ne.symm hrp) (Ne.symm hrq) hr with A | A | A | A <;> tauto
  have B : (r'.val.val = k₁ ∨ r'.val.val = -k₁) ∨ (r'.val.val = k₂ ∨ r'.val.val = -k₂) := by
    rcases rep_of_collinear hpq (Ne.symm hr'p) (Ne.symm hr'q) hr' with B | B | B | B <;> tauto
  have same : ∀ k : Charge, (r.val.val = k ∨ r.val.val = -k) →
      (r'.val.val = k ∨ r'.val.val = -k) → False := by
    intro k h1 h2
    apply hrr
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact rep_injective (h1.trans h2.symm)
    · exact absurd (h1.trans (by rw [h2, neg_neg])) (rep_ne_neg r r')
    · exact absurd (h1.trans (by rw [h2])) (rep_ne_neg r r')
    · exact rep_injective (h1.trans h2.symm)
  rcases A with A | A <;> rcases B with B | B
  · exact (same _ A B).elim
  · rw [pointPlane_of_rep r A, pointPlane_of_rep r' B]
  · rw [pointPlane_of_rep r A, pointPlane_of_rep r' B]
    exact sup_comm (gradedPlane ρ k₁) (gradedPlane ρ k₂)
  · exact (same _ A B).elim

/-- Ternary grading theorem (iv), shares. -/
theorem graded_share (hρ : IsTernaryGrading ρ) (p q r : SignedPlaneIndex) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    shareOfThreePlanes nativeEqualCubic (pointPlane ρ p) (pointPlane ρ q) (pointPlane ρ r) =
      if signedCollinear p q r then 1 else 0 := by
  have hb := planeShare_bounds nativeEqualCubic (gradedDecomposition hρ) p q r
  show planeShare nativeEqualCubic (gradedDecomposition hρ) p q r = _
  split_ifs with hcol
  · apply hb.2.1.mpr
    show pointPlane ρ r ≤ mixedProductSpace _ (pointPlane ρ p) (pointPlane ρ q)
    rw [mixed_eq hρ hpq]
    rcases rep_of_collinear hpq hpr hqr hcol with A | A | A | A
    · rw [pointPlane_of_rep r (Or.inl A)]; exact le_sup_left
    · rw [pointPlane_of_rep r (Or.inr A)]; exact le_sup_left
    · rw [pointPlane_of_rep r (Or.inl A)]; exact le_sup_right
    · rw [pointPlane_of_rep r (Or.inr A)]; exact le_sup_right
  · apply hb.2.2.mpr
    show (pointPlane ρ r).IsOrtho (mixedProductSpace _ (pointPlane ρ p) (pointPlane ρ q))
    rw [mixed_eq hρ hpq, Submodule.isOrtho_sup_right]
    have ne1 : ∀ k, (r.val.val = k ∨ r.val.val = -k) → k = p.val.val + q.val.val ∨
        k = p.val.val - q.val.val → False := by
      intro k hk hk'
      apply hcol
      apply collinear_of_rep hpq
      rcases hk with hk | hk <;> rcases hk' with hk' | hk' <;> rw [hk, hk'] <;> tauto
    constructor
    · apply gradedPlane_orthogonal hρ
      · intro e; exact ne1 _ (Or.inr (eq_neg_of_add_eq_zero_left e)) (Or.inl rfl)
      · intro e; exact ne1 _ (Or.inl (sub_eq_zero.mp e)) (Or.inl rfl)
    · apply gradedPlane_orthogonal hρ
      · intro e; exact ne1 _ (Or.inr (eq_neg_of_add_eq_zero_left e)) (Or.inr rfl)
      · intro e; exact ne1 _ (Or.inl (sub_eq_zero.mp e)) (Or.inr rfl)

end

end ThirteenPlanes.AlbertGrading.Grading
