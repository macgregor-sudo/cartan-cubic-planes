module

public import ThirteenPlanes.AlbertGrading.Recognition.CoreLemmas

@[expose] public section

/-!
# Systems of thirteen frames of `J_T`

`TitsSystem P` records what the proof of the recognition of systems with 52 positive shares uses about a sparsest system after
transport to `J_T`: frames, pairwise unbiasedness, and every pair lying in a quartet whose other two
planes lie in the product space (proof of the thirteen-plane support and incidence theorem, (c)⇒(b), through plane-share sum rule).
The product space is taken with the unit adjoined, `span_ℝ({e} ∪ U ∘ U')`, which contains the
centered products `x*y = x∘y − ⅓⟨x,y⟩e`.
-/

open scoped Matrix BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-- `span_ℝ({e} ∪ {x ∘ y | x ∈ U, y ∈ U'})`. -/
def titsProdSpace (U U' : Submodule ℝ CompactTits) : Submodule ℝ CompactTits :=
  Submodule.span ℝ ({CompactTits.one} ∪ Set.image2 CompactTits.product U U')

/-- Thirteen frames of `J_T`, pairwise unbiased, each pair in a quartet. -/
structure TitsSystem (P : Fin 13 → ZMod 3 → CompactTits) : Prop where
  frame : ∀ i, IsTitsFrame (P i)
  unbiased : ∀ i j, i ≠ j → ∀ a b,
    CompactTits.trace (CompactTits.product (P i a) (P j b)) = 1 / 3
  quartet : ∀ i j, i ≠ j → ∃ B : Finset (Fin 13), B.card = 4 ∧ i ∈ B ∧ j ∈ B ∧
    ∀ t ∈ B, t ≠ i → t ≠ j →
      titsFramePlane (P t) ≤ titsProdSpace (titsFramePlane (P i)) (titsFramePlane (P j))

theorem titsFramePlane_eq (p : ZMod 3 → CompactTits) :
    titsFramePlane p =
      Submodule.span ℝ ((fun x => x - (1 / 3 : ℝ) • CompactTits.one) '' Set.range p) := by
  rw [titsFramePlane, ← Set.range_comp]; rfl

theorem titsFramePlane_congr {p q : ZMod 3 → CompactTits} (h : Set.range p = Set.range q) :
    titsFramePlane p = titsFramePlane q := by
  rw [titsFramePlane_eq, titsFramePlane_eq, h]

theorem titsFramePlane_map {f : CompactTits ≃ₗ[ℝ] CompactTits} (hf : IsTraceAut f)
    (p : ZMod 3 → CompactTits) :
    titsFramePlane (fun a => f (p a)) = (titsFramePlane p).map f.toLinearMap := by
  rw [titsFramePlane, titsFramePlane, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  simp [hf.map_one]

theorem titsProdSpace_map {f : CompactTits ≃ₗ[ℝ] CompactTits} (hf : IsTraceAut f)
    (U U' : Submodule ℝ CompactTits) :
    (titsProdSpace U U').map f.toLinearMap ≤
      titsProdSpace (U.map f.toLinearMap) (U'.map f.toLinearMap) := by
  rw [titsProdSpace, Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨z, hz, rfl⟩
  rcases hz with hz | ⟨x, hx, y, hy, rfl⟩
  · left; rw [Set.mem_singleton_iff.mp hz]; exact hf.map_one
  · right; exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, (hf.1 x y).symm⟩

theorem TitsSystem.map {P : Fin 13 → ZMod 3 → CompactTits} (hS : TitsSystem P)
    {f : CompactTits ≃ₗ[ℝ] CompactTits} (hf : IsTraceAut f) :
    TitsSystem (fun i a => f (P i a)) where
  frame i := ⟨fun a b => by rw [← hf.1, (hS.frame i).1 a b]; split <;> simp,
    fun a => by rw [hf.2, (hS.frame i).2.1], by rw [← map_sum, (hS.frame i).2.2, hf.map_one]⟩
  unbiased i j hij a b := by rw [← hf.1, hf.2]; exact hS.unbiased i j hij a b
  quartet i j hij := by
    obtain ⟨B, hB, hi, hj, hle⟩ := hS.quartet i j hij
    refine ⟨B, hB, hi, hj, fun t ht hti htj => ?_⟩
    rw [titsFramePlane_map hf, titsFramePlane_map hf, titsFramePlane_map hf]
    exact (Submodule.map_mono (hle t ht hti htj)).trans (titsProdSpace_map hf _ _)

theorem frame_injective {p : ZMod 3 → CompactTits} (hp : IsTitsFrame p) : Function.Injective p := by
  intro a b hab
  by_contra hne
  have h1 := hp.1 a b
  rw [if_neg hne, ← hab, hp.1 a a, if_pos rfl] at h1
  have := hp.2.1 a
  rw [h1, map_zero] at this
  norm_num at this

theorem TitsSystem.range_ne {P : Fin 13 → ZMod 3 → CompactTits} (hS : TitsSystem P) {i j : Fin 13}
    (hij : i ≠ j) : Set.range (P i) ≠ Set.range (P j) := by
  intro h
  obtain ⟨b, hb⟩ : P i 0 ∈ Set.range (P j) := h ▸ Set.mem_range_self 0
  have := hS.unbiased i j hij 0 b
  rw [← hb, (hS.frame j).1 b b, if_pos rfl, (hS.frame j).2.1] at this
  norm_num at this

/-! ## Graded planes and their products -/

/-- `span_ℂ{u_g, u_{-g}}`. -/
def gradedLine (g : Charge) : Submodule ℂ (FirstTits ℂ) :=
  Submodule.span ℂ {titsBasis g, titsBasis (-g)}

theorem gradedPlane_coords (g : Charge) {x : CompactTits}
    (hx : x ∈ titsFramePlane (gradedFrame g)) : CompactTits.coordinates x ∈ gradedLine g := by
  have hle : titsFramePlane (gradedFrame g) ≤
      ((gradedLine g).restrictScalars ℝ).comap CompactTits.coordinates := by
    rw [titsFramePlane, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    change CompactTits.coordinates (gradedFrame g a - (1 / 3 : ℝ) • CompactTits.one) ∈ gradedLine g
    rw [map_sub, map_smul, gradedFrame_coordinates, CompactTits.coordinates_one, gradedCoords,
      ← Complex.coe_smul]
    have e : (1 / 3 : ℂ) • (firstTitsOne + chargePhase (-a) • titsBasis g +
        chargePhase a • titsBasis (-g)) - (((1 / 3 : ℝ) : ℂ)) • (firstTitsOne : FirstTits ℂ) =
        ((1 / 3 : ℂ) * chargePhase (-a)) • titsBasis g +
          ((1 / 3 : ℂ) * chargePhase a) • titsBasis (-g) := by
      push_cast; module
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  exact hle hx

/-- `span_ℂ{e, u_{g+h}, u_{-g-h}, u_{g-h}, u_{-g+h}}`. -/
def mixedSpan (g h : Charge) : Submodule ℂ (FirstTits ℂ) :=
  Submodule.span ℂ {firstTitsOne, titsBasis (g + h), titsBasis (-g + -h), titsBasis (g + -h),
    titsBasis (-g + h)}

theorem product_mem_mixedSpan {g h : Charge} (hd : ¬ F3Dependent g h) {x y : FirstTits ℂ}
    (hx : x ∈ gradedLine g) (hy : y ∈ gradedLine h) : firstTitsJordanProduct x y ∈ mixedSpan g h := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  obtain ⟨c1, -, e1⟩ := titsBasis_indep g h hd
  obtain ⟨c2, -, e2⟩ := titsBasis_indep g (-h) (by
    simpa using indep_of_signs hd 1 (-1) one_ne_zero (by decide))
  obtain ⟨c3, -, e3⟩ := titsBasis_indep (-g) h (by
    simpa using indep_of_signs hd (-1) 1 (by decide) one_ne_zero)
  obtain ⟨c4, -, e4⟩ := titsBasis_indep (-g) (-h) (by
    simpa using indep_of_signs hd (-1) (-1) (by decide) (by decide))
  simp only [← firstTitsJordanBilinear_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [firstTitsJordanBilinear_apply, e1, e2, e3, e4]
  repeat' first
    | refine Submodule.add_mem _ ?_ ?_
    | refine Submodule.smul_mem _ _ ?_
    | exact Submodule.subset_span (by simp)

theorem charge_ne_zero_of_indep {g h : Charge} (hd : ¬ F3Dependent g h) :
    g + h ≠ 0 ∧ g + -h ≠ 0 := by
  constructor
  · intro e; exact hd ⟨1, 1, Or.inl one_ne_zero, by simpa using e⟩
  · intro e; exact hd ⟨1, -1, Or.inl one_ne_zero, by simpa [neg_smul] using e⟩

theorem indep_sum_diff {g h : Charge} (hd : ¬ F3Dependent g h) :
    ¬ F3Dependent (g + h) (g + -h) := by
  rintro ⟨a, b, hab, he⟩
  have key : a + b = 0 ∧ a - b = 0 := by
    by_contra hne
    apply hd
    refine ⟨a + b, a - b, ?_, ?_⟩
    · by_contra h'
      push_neg at h'
      exact hne h'
    · rw [← he]; simp only [add_smul, sub_smul, smul_add, smul_neg]; abel
  have : ∀ a b : ZMod 3, a + b = 0 → a - b = 0 → a = 0 ∧ b = 0 := by decide
  obtain ⟨ha, hb⟩ := this a b key.1 key.2
  rcases hab with h | h
  · exact h ha
  · exact h hb

/-- A frame whose plane lies in the product space of two graded planes of independent `g, h` is,
as a set, the graded frame of `g + h` or of `g - h`. -/
theorem graded_of_planes {P : ZMod 3 → CompactTits} (hP : IsTitsFrame P) {g h : Charge}
    (hd : ¬ F3Dependent g h)
    (hle : titsFramePlane P ≤
      titsProdSpace (titsFramePlane (gradedFrame g)) (titsFramePlane (gradedFrame h))) :
    Set.range P = Set.range (gradedFrame (g + h)) ∨
      Set.range P = Set.range (gradedFrame (g + -h)) := by
  have hprod : titsProdSpace (titsFramePlane (gradedFrame g)) (titsFramePlane (gradedFrame h)) ≤
      ((mixedSpan g h).restrictScalars ℝ).comap CompactTits.coordinates := by
    rw [titsProdSpace, Submodule.span_le]
    rintro _ (hz | ⟨x, hx, y, hy, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hz]
      change CompactTits.coordinates CompactTits.one ∈ mixedSpan g h
      rw [CompactTits.coordinates_one]
      exact Submodule.subset_span (by simp)
    · change CompactTits.coordinates (CompactTits.product x y) ∈ mixedSpan g h
      rw [coordinates_product]
      exact product_mem_mixedSpan hd (gradedPlane_coords g hx) (gradedPlane_coords h hy)
  have hmem : titsContrast P ∈ mixedSpan g h := by
    apply contrast_mem_of_coordinates
    intro a
    have h1 : P a - (1 / 3 : ℝ) • CompactTits.one ∈ titsFramePlane P :=
      Submodule.subset_span ⟨a, rfl⟩
    have h2 := hprod (hle h1)
    change CompactTits.coordinates (P a - (1 / 3 : ℝ) • CompactTits.one) ∈ mixedSpan g h at h2
    have e : CompactTits.coordinates (P a) =
        CompactTits.coordinates (P a - (1 / 3 : ℝ) • CompactTits.one) +
          (((1 / 3 : ℝ) : ℂ)) • firstTitsOne := by
      rw [Complex.coe_smul, map_sub, map_smul, CompactTits.coordinates_one, sub_add_cancel]
    rw [e]
    exact Submodule.add_mem _ h2 (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨hs0, hd0⟩ := charge_ne_zero_of_indep hd
  have hT : mixedSpan g h = Submodule.span ℂ {firstTitsOne, titsBasis (g + h),
      titsBasis (-(g + h)), titsBasis (g + -h), titsBasis (-(g + -h))} := by
    rw [mixedSpan, neg_add, neg_add, neg_neg]
  rw [hT] at hmem
  rcases contrast_four hP (indep_sum_diff hd) hmem with h1 | h1
  · left
    obtain ⟨l, hl | hl⟩ := contrast_two hP hs0 h1
    · exact range_eq_of_line hP hl
    · rw [range_eq_of_line hP hl, range_gradedFrame_neg]
  · right
    obtain ⟨l, hl | hl⟩ := contrast_two hP hd0 h1
    · exact range_eq_of_line hP hl
    · rw [range_eq_of_line hP hl, range_gradedFrame_neg]

end

end ThirteenPlanes.AlbertGrading
