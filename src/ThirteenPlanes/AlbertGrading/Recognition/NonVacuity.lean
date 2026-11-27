module

public import ThirteenPlanes.AlbertGrading.Recognition.Main

@[expose] public section

/-!
# Non-vacuity of the recognition of the graded frame system

The graded system of the first-Tits grading and Weyl basis itself (one graded frame for each of the thirteen points)
satisfies all hypotheses of `Targets.Recognition`; proved directly, not through the proposition.
-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem gradedFrame_isFrame {g : Charge} (hg : g ≠ 0) : IsTitsFrame (gradedFrame g) := by
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  have hgg := charge_add_self g
  have hp4 : chargeRoot ^ 4 = chargeRoot := by linear_combination chargeRoot * hc
  have hp2 : chargeRoot ^ 2 = -chargeRoot - 1 := by linear_combination hq
  have hp5 : chargeRoot ^ 5 = -chargeRoot - 1 := by linear_combination chargeRoot ^ 2 * hc + hq
  have hp6 : chargeRoot ^ 6 = 1 := by linear_combination (chargeRoot ^ 3 + 1) * hc
  have h1 : firstTitsJordanProduct (titsBasis g) (titsBasis g) = titsBasis (-g) := by
    rw [titsBasis_product_dependent _ _ (dep_self g), hgg]
  have h2 : firstTitsJordanProduct (titsBasis (-g)) (titsBasis (-g)) = titsBasis g := by
    rw [titsBasis_product_dependent _ _ (dep_neg_neg g), charge_add_self, neg_neg]
  have h3 : firstTitsJordanProduct (titsBasis g) (titsBasis (-g)) = firstTitsOne := by
    rw [titsBasis_product_dependent _ _ (dep_neg g), add_neg_cancel, titsBasis_zero]
  have h4 : firstTitsJordanProduct (titsBasis (-g)) (titsBasis g) = firstTitsOne := by
    rw [firstTitsJordanProduct_comm, h3]
  have h5 : ∀ x, firstTitsJordanProduct firstTitsOne x = x := firstTitsJordanProduct_one_left
  have h6 : ∀ x, firstTitsJordanProduct x firstTitsOne = x := fun x => by
    rw [firstTitsJordanProduct_comm, firstTitsJordanProduct_one_left]
  refine ⟨fun a b => CompactTits.ext ?_, fun a => ?_, CompactTits.ext ?_⟩
  · rw [coordinates_product, gradedFrame_coordinates, gradedFrame_coordinates]
    simp only [gradedCoords, ← firstTitsJordanBilinear_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply]
    simp only [firstTitsJordanBilinear_apply, h1, h2, h3, h4, h5, h6]
    rcases zmod3_cases a with rfl | rfl | rfl <;> rcases zmod3_cases b with rfl | rfl | rfl <;>
      simp only [show (0 : ZMod 3) ≠ 1 by decide, show (0 : ZMod 3) ≠ 2 by decide,
        show (1 : ZMod 3) ≠ 0 by decide, show (1 : ZMod 3) ≠ 2 by decide,
        show (2 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 1 by decide, if_true, if_false,
        ite_true, ite_false, gradedFrame_coordinates, gradedCoords,
        map_zero, neg_zero, chargePhase_zero, cpn1, cpn2, cp1, cp2] <;>
      match_scalars <;>
      first
      | ring1
      | (ring_nf; simp only [hp6, hp5, hp4, hc, hp2]; ring1)
  · have ht : ((CompactTits.trace (gradedFrame g a) : ℝ) : ℂ) = 1 := by
      rw [CompactTits.complex_trace_eq, ← tr1_apply, gradedFrame_coordinates, gradedCoords]
      simp only [map_smul, map_add, tr1_one, tr1_titsBasis, if_neg hg,
        if_neg (neg_ne_zero.mpr hg), smul_eq_mul, mul_zero, add_zero]
      norm_num
    exact_mod_cast ht
  · rw [map_sum, CompactTits.coordinates_one, sum_zmod3]
    simp only [gradedFrame_coordinates, gradedCoords, neg_zero, chargePhase_zero, cpn1, cpn2,
      cp1, cp2]
    match_scalars <;> first
      | ring1
      | (ring_nf; simp only [hp6, hp5, hp4, hc, hp2]; ring1)

theorem charge_point_cover : ∀ g : Charge, g ≠ 0 → ∃ m, g = pointRep m ∨ g = -pointRep m := by
  decide

theorem pointRep_indep : ∀ m n : Fin 13, m ≠ n → ¬ F3Dependent (pointRep m) (pointRep n) := by
  unfold F3Dependent
  decide

theorem recognition_hypotheses_satisfiable :
    let F : Fin 13 → ZMod 3 → CompactTits := fun m => gradedFrame (pointRep m)
    (∀ i, IsTitsFrame (F i)) ∧
    (∀ v : WeylLabel, v ≠ 0 → ∃ i, Set.range (F i) = Set.range (weylEigenframe v)) ∧
    (∃ i, Set.range (F i) = Set.range exteriorPoint) ∧
    (∀ i j, Set.range (F i) ≠ Set.range (F j) →
      ∀ x ∈ ({titsContrast (F i), compactInvolution (titsContrast (F i))} : Set (FirstTits ℂ)),
      ∀ y ∈ ({titsContrast (F j), compactInvolution (titsContrast (F j))} : Set (FirstTits ℂ)),
      ∃ c : ℂ, c ≠ 0 ∧ ∃ m ∈ titsContrastLines F, firstTitsJordanProduct x y = c • m) := by
  intro F
  refine ⟨fun i => gradedFrame_isFrame (pointRep_ne_zero i), fun v hv => ?_, ⟨4, ?_⟩, ?_⟩
  · obtain ⟨m, -, hm⟩ := visible_classes v hv
    refine ⟨m, ?_⟩
    change Set.range (gradedFrame (pointRep m)) = Set.range (gradedFrame (chargeFrom v 0))
    rcases hm with e | e
    · rw [e]
    · rw [e, range_gradedFrame_neg]
  · exact (exterior_range).symm
  · intro i j hij x hx y hy
    have hne : i ≠ j := by rintro rfl; exact hij rfl
    have hd := pointRep_indep i j hne
    simp only [F, gradedFrame_contrast, titsBasis_involution] at hx hy
    -- `x = u_{s g}`, `y = u_{t h}` with signs
    have hxs : ∃ s : ZMod 3, s ≠ 0 ∧ x = titsBasis (s • pointRep i) := by
      rcases hx with rfl | rfl
      · exact ⟨1, one_ne_zero, by rw [one_smul]⟩
      · exact ⟨-1, by decide, by rw [neg_smul, one_smul]⟩
    have hyt : ∃ t : ZMod 3, t ≠ 0 ∧ y = titsBasis (t • pointRep j) := by
      rcases hy with rfl | rfl
      · exact ⟨1, one_ne_zero, by rw [one_smul]⟩
      · exact ⟨-1, by decide, by rw [neg_smul, one_smul]⟩
    obtain ⟨s, hs, rfl⟩ := hxs
    obtain ⟨t, ht, rfl⟩ := hyt
    have hd' := indep_of_signs hd s t hs ht
    obtain ⟨c, hc, he⟩ := titsBasis_indep _ _ hd'
    have hsum : s • pointRep i + t • pointRep j ≠ 0 := by
      intro e; exact hd' ⟨1, 1, Or.inl one_ne_zero, by simpa using e⟩
    obtain ⟨k, hk | hk⟩ := charge_point_cover _ hsum
    · refine ⟨c, hc, titsContrast (F k), Or.inl (Or.inr ⟨k, rfl⟩), ?_⟩
      rw [he, hk]
      simp only [F, gradedFrame_contrast]
    · refine ⟨c, hc, compactInvolution (titsContrast (F k)), Or.inr ⟨k, rfl⟩, ?_⟩
      rw [he, hk]
      simp only [F, gradedFrame_contrast, titsBasis_involution]

end

end ThirteenPlanes.AlbertGrading
