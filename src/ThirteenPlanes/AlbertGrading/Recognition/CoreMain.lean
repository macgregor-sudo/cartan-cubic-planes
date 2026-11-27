module

public import ThirteenPlanes.AlbertGrading.Recognition.Core

@[expose] public section

/-! Recognition of the sparsest plane systems in first Tits coordinates. -/

open scoped Matrix BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem exists_not_mem' {B : Finset (Fin 13)} (hB : B.card < 13) : ∃ H, H ∉ B := by
  by_contra h
  push_neg at h
  have : B = Finset.univ := Finset.eq_univ_of_forall h
  rw [this, Finset.card_univ, Fintype.card_fin] at hB
  exact lt_irrefl _ hB

theorem not_dep_pointRep (m n : Fin 13)
    (h : (m, n) ∈ ({(0, 1), (0, 4), (1, 4), (2, 4), (3, 4)} : Finset (Fin 13 × Fin 13))) :
    ¬ F3Dependent (pointRep m) (pointRep n) := by
  unfold F3Dependent
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem fix_visible {f : CompactTits ≃ₗ[ℝ] CompactTits}
    (hfix : ∀ x, (CompactTits.coordinates x).2.1 = 0 → f x = x) {p : ZMod 3 → CompactTits}
    {v : WeylLabel} (hp : Set.range p = Set.range (gradedFrame (chargeFrom v 0))) :
    (fun a => f (p a)) = p := by
  funext a
  obtain ⟨b, hb⟩ : p a ∈ Set.range (gradedFrame (chargeFrom v 0)) := hp ▸ Set.mem_range_self a
  apply hfix
  rw [← hb]
  exact eigen_hidden_zero v b

/-- The `J_T` core of the recognition of systems with 52 positive shares, given the pair normalization. -/
theorem core_normalize (hN : OrbitHypotheses.PairNormalization) {P : Fin 13 → ZMod 3 → CompactTits}
    (hS : TitsSystem P) :
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTraceAut f ∧ ∃ σ : Fin 13 ≃ Fin 13,
      ∀ i, Set.range (fun a => f (P i a)) = Set.range (gradedFrame (pointRep (σ i))) := by
  classical
  have h01 : (0 : Fin 13) ≠ 1 := by decide
  -- normalizing the pair `0, 1`
  obtain ⟨f₁, hf₁a, hf₁t, h0, h1⟩ :=
    hN (P 0) (P 1) (hS.frame 0) (hS.frame 1) (hS.unbiased 0 1 h01)
  have hf₁ : IsTraceAut f₁ := ⟨hf₁a, hf₁t⟩
  set Q : Fin 13 → ZMod 3 → CompactTits := fun i a => f₁ (P i a) with hQdef
  have hQ : TitsSystem Q := hS.map hf₁
  have hQ0 : Set.range (Q 0) = Set.range (gradedFrame (pointRep 0)) := h0
  have hQ1 : Set.range (Q 1) = Set.range (gradedFrame (pointRep 1)) := h1
  -- the other two frames of the quartet
  obtain ⟨⟨s2, hs2⟩, ⟨s3, hs3⟩⟩ := quartet_step hQ h01 (not_dep_pointRep 0 1 (by decide)) hQ0 hQ1
  rw [show pointRep 0 + pointRep 1 = pointRep 2 by decide] at hs2
  rw [show pointRep 0 + -pointRep 1 = pointRep 3 by decide] at hs3
  -- an exterior frame
  obtain ⟨H, hH⟩ := exists_not_mem' (B := {0, 1, s2, s3})
    (lt_of_le_of_lt (Finset.card_le_four) (by decide))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hH
  obtain ⟨hH0, hH1, hH2, hH3⟩ := hH
  have hvisQ : ∀ m : Fin 13, (m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) →
      ∃ i, i ≠ H ∧ Set.range (Q i) = Set.range (gradedFrame (pointRep m)) := by
    rintro m (rfl | rfl | rfl | rfl)
    exacts [⟨0, Ne.symm hH0, hQ0⟩, ⟨1, Ne.symm hH1, hQ1⟩, ⟨s2, Ne.symm hH2, hs2⟩,
      ⟨s3, Ne.symm hH3, hs3⟩]
  have horth : (titsFramePlane (Q H)).IsOrtho visibleTraceless := by
    apply exterior_orthogonal (hQ.frame H)
    intro v hv a b
    obtain ⟨m, hm, hvm⟩ := visible_classes v hv
    obtain ⟨i, hiH, hi⟩ := hvisQ m hm
    have hmem : gradedFrame (chargeFrom v 0) b ∈ Set.range (Q i) := by
      rw [hi]
      rcases hvm with e | e
      · rw [e]; exact Set.mem_range_self b
      · rw [e, gradedFrame_neg]; exact Set.mem_range_self _
    obtain ⟨a', ha'⟩ := hmem
    rw [← ha']
    exact hQ.unbiased H i (Ne.symm hiH) a a'
  obtain ⟨π, V, -, -, -, ⟨f₂, hf₂a, hf₂c, hf₂p, hf₂fix⟩, -, -⟩ :=
    exteriorFrame (Q H) (hQ.frame H) horth
  have hf₂ : IsTraceAut f₂ := ⟨hf₂a, fun x => by
    rw [CompactTits.trace_apply, CompactTits.trace_apply, hf₂c]; rfl⟩
  set R : Fin 13 → ZMod 3 → CompactTits := fun i a => f₂ (Q i a) with hRdef
  have hR : TitsSystem R := hQ.map hf₂
  have hRH : Set.range (R H) = Set.range (gradedFrame (pointRep 4)) := by
    rw [show pointRep 4 = chargeFrom 0 2 from rfl, ← exterior_range]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨π.symm a, ?_⟩
      rw [← hf₂p, Equiv.apply_symm_apply]
    · rintro ⟨b, rfl⟩
      exact ⟨π b, hf₂p b⟩
  have hvisR : ∀ m : Fin 13, (m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) →
      ∃ i, i ≠ H ∧ Set.range (R i) = Set.range (gradedFrame (pointRep m)) := by
    intro m hm
    obtain ⟨i, hiH, hi⟩ := hvisQ m hm
    refine ⟨i, hiH, ?_⟩
    have hRi : R i = Q i := by
      rcases hm with rfl | rfl | rfl | rfl
      · exact fix_visible hf₂fix (v := (0, 1)) hi
      · exact fix_visible hf₂fix (v := (1, 0)) hi
      · exact fix_visible hf₂fix (v := (1, 1)) hi
      · exact fix_visible hf₂fix (v := (2, 1)) hi
    rw [hRi, hi]
  -- the eight remaining points
  have hmixed : ∀ m : Fin 13, (m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) →
      (∃ s, Set.range (R s) = Set.range (gradedFrame (pointRep m + pointRep 4))) ∧
        (∃ s, Set.range (R s) = Set.range (gradedFrame (pointRep m + -pointRep 4))) := by
    intro m hm
    obtain ⟨i, hiH, hi⟩ := hvisR m hm
    refine quartet_step hR hiH (not_dep_pointRep m 4 ?_) hi hRH
    rcases hm with rfl | rfl | rfl | rfl <;> decide
  have hAtt : ∀ m : Fin 13, ∃ i, Set.range (R i) = Set.range (gradedFrame (pointRep m)) := by
    have e0 := hmixed 0 (by decide)
    have e1 := hmixed 1 (by decide)
    have e2 := hmixed 2 (by decide)
    have e3 := hmixed 3 (by decide)
    rw [show pointRep 0 + pointRep 4 = pointRep 5 by decide,
      show pointRep 0 + -pointRep 4 = pointRep 6 by decide] at e0
    rw [show pointRep 1 + pointRep 4 = pointRep 7 by decide,
      show pointRep 1 + -pointRep 4 = pointRep 8 by decide] at e1
    rw [show pointRep 2 + pointRep 4 = pointRep 9 by decide,
      show pointRep 2 + -pointRep 4 = pointRep 10 by decide] at e2
    rw [show pointRep 3 + pointRep 4 = pointRep 11 by decide,
      show pointRep 3 + -pointRep 4 = pointRep 12 by decide] at e3
    intro m
    fin_cases m
    · obtain ⟨i, -, hi⟩ := hvisR 0 (by decide); exact ⟨i, hi⟩
    · obtain ⟨i, -, hi⟩ := hvisR 1 (by decide); exact ⟨i, hi⟩
    · obtain ⟨i, -, hi⟩ := hvisR 2 (by decide); exact ⟨i, hi⟩
    · obtain ⟨i, -, hi⟩ := hvisR 3 (by decide); exact ⟨i, hi⟩
    · exact ⟨H, hRH⟩
    · exact e0.1
    · exact e0.2
    · exact e1.1
    · exact e1.2
    · exact e2.1
    · exact e2.2
    · exact e3.1
    · exact e3.2
  choose ι hι using hAtt
  have hιinj : Function.Injective ι := by
    intro m n hmn
    apply pointRep_injective_range
    rw [← hι m, ← hι n, hmn]
  have hιbij : Function.Bijective ι := Finite.injective_iff_bijective.mp hιinj
  let e : Fin 13 ≃ Fin 13 := Equiv.ofBijective ι hιbij
  refine ⟨f₁.trans f₂, hf₁.trans hf₂, e.symm, fun i => ?_⟩
  have hi : ι (e.symm i) = i := e.apply_symm_apply i
  change Set.range (R i) = _
  conv_lhs => rw [← hi]
  exact hι _

end

end ThirteenPlanes.AlbertGrading
