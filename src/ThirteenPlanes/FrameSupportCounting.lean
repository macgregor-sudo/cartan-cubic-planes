/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FrameSupportWeights

@[expose] public section

set_option backward.privateInPublic true

/-! Appendix support bound from pairwise unbiasedness, from the fixed-pair sum to genuine unordered
triples. -/

noncomputable section

namespace ThirteenPlanes

open scoped BigOperators

private theorem sumSwapFirst {ι : Type*} [Fintype ι] (F : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, F b a c) = ∑ a, ∑ b, ∑ c, F a b c := Finset.sum_comm

private theorem sumSwapLast {ι : Type*} [Fintype ι] (F : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, F a c b) = ∑ a, ∑ b, ∑ c, F a b c := by
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem sumCycle {ι : Type*} [Fintype ι] (F : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, F b c a) = ∑ a, ∑ b, ∑ c, F a b c := by
  rw [sumSwapFirst (fun a b c => F a c b), sumSwapLast F]

private theorem sumCycleTwice {ι : Type*} [Fintype ι] (F : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, F c a b) = ∑ a, ∑ b, ∑ c, F a b c := by
  rw [sumSwapLast (fun a b c => F b a c), sumSwapFirst F]

private theorem sumReverse {ι : Type*} [Fintype ι] (F : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, F c b a) = ∑ a, ∑ b, ∑ c, F a b c := by
  rw [sumSwapFirst (fun a b c => F c a b), sumCycleTwice F]

theorem TightNativeCode.frameWeight_eq_cubic (c : TightNativeCode) (f g h : Fin 13) :
    c.frameWeight f g h = 6 * ∑ k : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
      (nativeEqualCubic.apply (c.frameVector f i) (c.frameVector g j) (c.frameVector h k)) ^ 2 := by
  unfold frameWeight
  simp only [Fintype.sum_prod_type]
  rfl

theorem TightNativeCode.frameWeight_swap (c : TightNativeCode) (f g h : Fin 13) :
    c.frameWeight f g h = c.frameWeight g f h := by
  rw [c.frameWeight_eq_cubic, c.frameWeight_eq_cubic]
  simp_rw [nativeEqualCubic.apply_swap₁₂ (c.frameVector g _)]
  exact congrArg (6 * ·) (sumSwapLast _).symm

theorem TightNativeCode.frameWeight_cycle (c : TightNativeCode) (f g h : Fin 13) :
    c.frameWeight f g h = c.frameWeight g h f := by
  have hcyc (x y z : NativeTraceless) :
      nativeEqualCubic.apply y z x = nativeEqualCubic.apply x y z :=
    (nativeEqualCubic.apply_swap₂₃ y z x).trans (nativeEqualCubic.apply_swap₁₂ y x z)
  rw [c.frameWeight_eq_cubic, c.frameWeight_eq_cubic]
  simp_rw [hcyc (c.frameVector f _) (c.frameVector g _) (c.frameVector h _)]
  exact congrArg (6 * ·) (sumCycleTwice _).symm

private def orderedFrameWeight (c : TightNativeCode) (f g h : Fin 13) : ℝ :=
  if f ≠ g ∧ h ≠ f ∧ h ≠ g then c.frameWeight f g h else 0

private def ascendingFrameWeight (c : TightNativeCode) (f g h : Fin 13) : ℝ :=
  if f < g ∧ g < h then c.frameWeight f g h else 0

private theorem orderedFrameWeight_eq_six_ascending (c : TightNativeCode) (f g h : Fin 13) :
    orderedFrameWeight c f g h =
      ascendingFrameWeight c f g h + ascendingFrameWeight c f h g +
      ascendingFrameWeight c g f h + ascendingFrameWeight c g h f +
      ascendingFrameWeight c h f g + ascendingFrameWeight c h g f := by
  have h₁ : c.frameWeight f h g = c.frameWeight f g h :=
    (c.frameWeight_cycle f h g).trans
      ((c.frameWeight_swap h g f).trans (c.frameWeight_cycle f g h).symm)
  have h₂ := c.frameWeight_swap g f h
  have h₃ := (c.frameWeight_cycle f g h).symm
  have h₄ := c.frameWeight_cycle h f g
  have h₅ := (c.frameWeight_swap h g f).trans h₃
  simp only [orderedFrameWeight, ascendingFrameWeight, h₁, h₂, h₃, h₄, h₅]
  simp only [Fin.lt_def, ne_eq, Fin.ext_iff]
  split_ifs <;> first | omega | ring

private theorem orderedFrameWeight_total (c : TightNativeCode) :
    (∑ f : Fin 13, ∑ g : Fin 13, ∑ h : Fin 13, orderedFrameWeight c f g h) = 312 := by
  have hpair (f g : Fin 13) :
      (∑ h, orderedFrameWeight c f g h) = if f ≠ g then (2 : ℝ) else 0 := by
    by_cases hfg : f ≠ g
    · rw [ite_eq_left hfg, ← c.frameWeight_pair_sum hfg]
      apply Finset.sum_congr rfl
      intro h _
      by_cases h₁ : h = f
      · subst h
        simp [orderedFrameWeight, c.frameWeight_repeated_left hfg]
      · by_cases h₂ : h = g
        · subst h
          simp [orderedFrameWeight, c.frameWeight_repeated_right hfg]
        · simp [orderedFrameWeight, hfg, h₁, h₂]
    · simp [orderedFrameWeight, hfg]
  have hrow (f : Fin 13) : (∑ g : Fin 13, if f ≠ g then (2 : ℝ) else 0) = 24 := by
    have h : (∑ g : Fin 13, if f ≠ g then (2 : ℝ) else 0) =
        (∑ _g : Fin 13, (2 : ℝ)) - ∑ g : Fin 13, if g = f then (2 : ℝ) else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro g _
      by_cases heq : g = f
      · subst g; simp
      · simp [heq, Ne.symm heq]
    rw [h]
    norm_num
  simp only [hpair, hrow]
  norm_num

/-- An unordered frame triple, enumerated in its unique increasing order. -/
abbrev NativeFrameTriple :=
  {fgh : Fin 13 × Fin 13 × Fin 13 // fgh.1 < fgh.2.1 ∧ fgh.2.1 < fgh.2.2}

def TightNativeCode.tripleWeight (c : TightNativeCode) (t : NativeFrameTriple) : ℝ :=
  c.frameWeight t.val.1 t.val.2.1 t.val.2.2

private theorem ascendingFrameWeight_eq_triple_sum (c : TightNativeCode) :
    (∑ f : Fin 13, ∑ g : Fin 13, ∑ h : Fin 13, ascendingFrameWeight c f g h) =
      ∑ t : NativeFrameTriple, c.tripleWeight t := by
  classical
  have h := Finset.sum_subtype
    (F := (inferInstance : Fintype NativeFrameTriple))
    (p := fun t : Fin 13 × Fin 13 × Fin 13 => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
    (Finset.univ.filter (fun t : Fin 13 × Fin 13 × Fin 13 =>
      t.1 < t.2.1 ∧ t.2.1 < t.2.2))
    (by intro t; simp)
    (fun t : Fin 13 × Fin 13 × Fin 13 => c.frameWeight t.1 t.2.1 t.2.2)
  simpa only [TightNativeCode.tripleWeight, Finset.sum_filter, Fintype.sum_prod_type,
    ascendingFrameWeight] using h

theorem TightNativeCode.tripleWeight_total (c : TightNativeCode) :
    (∑ t : NativeFrameTriple, c.tripleWeight t) = 52 := by
  have h : (∑ f, ∑ g, ∑ h, orderedFrameWeight c f g h) =
      6 * (∑ f, ∑ g, ∑ h, ascendingFrameWeight c f g h) := by
    simp_rw [orderedFrameWeight_eq_six_ascending]
    simp only [Finset.sum_add_distrib]
    rw [sumSwapLast (ascendingFrameWeight c), sumSwapFirst (ascendingFrameWeight c),
      sumCycle (ascendingFrameWeight c), sumCycleTwice (ascendingFrameWeight c),
      sumReverse (ascendingFrameWeight c)]
    ring
  rw [orderedFrameWeight_total c, ascendingFrameWeight_eq_triple_sum] at h
  linarith

theorem TightNativeCode.tripleWeight_mem_unitInterval (c : TightNativeCode) (t : NativeFrameTriple) :
    c.tripleWeight t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨c.frameWeight_nonneg _ _ _, c.frameWeight_le_one (ne_of_lt t.property.1) _⟩

def TightNativeCode.tripleSupport (c : TightNativeCode) : Finset NativeFrameTriple :=
  Finset.univ.filter (fun t => c.tripleWeight t ≠ 0)

def TightNativeCode.supportEnergy (c : TightNativeCode) : ℝ :=
  ∑ t : NativeFrameTriple, c.tripleWeight t * (1 - c.tripleWeight t)

theorem TightNativeCode.supportWeight_sum (c : TightNativeCode) :
    (∑ t ∈ c.tripleSupport, c.tripleWeight t) = 52 := by
  rw [tripleSupport, Finset.sum_filter, ← c.tripleWeight_total]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : c.tripleWeight t = 0 <;> simp [ht]

theorem TightNativeCode.support_card_ge_fifty_two (c : TightNativeCode) : 52 ≤ c.tripleSupport.card := by
  have h : (52 : ℝ) ≤ c.tripleSupport.card := by
    calc
      _ = ∑ t ∈ c.tripleSupport, c.tripleWeight t := c.supportWeight_sum.symm
      _ ≤ ∑ _t ∈ c.tripleSupport, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ => (c.tripleWeight_mem_unitInterval t).2
      _ = _ := by simp
  exact_mod_cast h

theorem TightNativeCode.supportEnergy_eq_zero_iff (c : TightNativeCode) :
    c.supportEnergy = 0 ↔ ∀ t, c.tripleWeight t = 0 ∨ c.tripleWeight t = 1 := by
  constructor
  · intro h t
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      mul_nonneg (c.tripleWeight_mem_unitInterval x).1
        (sub_nonneg.mpr (c.tripleWeight_mem_unitInterval x).2))).mp h t (Finset.mem_univ t)
    rcases mul_eq_zero.mp hz with h₀ | h₁
    · exact Or.inl h₀
    · exact Or.inr (sub_eq_zero.mp h₁).symm
  · intro hs
    apply Finset.sum_eq_zero
    intro t _
    rcases hs t with ht | ht <;> simp [ht]

theorem TightNativeCode.support_eq_fifty_two_iff_energy_zero (c : TightNativeCode) :
    c.tripleSupport.card = 52 ↔ c.supportEnergy = 0 := by
  constructor
  · intro hcard
    have h : (∑ t ∈ c.tripleSupport, (1 - c.tripleWeight t)) = 0 := by
      rw [Finset.sum_sub_distrib, c.supportWeight_sum]
      simp [hcard]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => sub_nonneg.mpr (c.tripleWeight_mem_unitInterval t).2)).mp h
    apply c.supportEnergy_eq_zero_iff.mpr
    intro t
    by_cases ht : c.tripleWeight t = 0
    · exact Or.inl ht
    · have hm : t ∈ c.tripleSupport := by simp [tripleSupport, ht]
      exact Or.inr (sub_eq_zero.mp (hz t hm)).symm
  · intro h
    have hs := c.supportEnergy_eq_zero_iff.mp h
    have hcard : (c.tripleSupport.card : ℝ) = 52 := by
      calc
        _ = ∑ _t ∈ c.tripleSupport, (1 : ℝ) := by simp
        _ = ∑ t ∈ c.tripleSupport, c.tripleWeight t := by
          apply Finset.sum_congr rfl
          intro t ht
          have hn : c.tripleWeight t ≠ 0 := (Finset.mem_filter.mp ht).2
          exact ((hs t).resolve_left hn).symm
        _ = _ := c.supportWeight_sum
    exact_mod_cast hcard

end ThirteenPlanes
