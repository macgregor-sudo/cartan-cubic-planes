module

public import ThirteenPlanes.Cartan.GradedLineRestrictionCore
public import ThirteenPlanes.Cartan.DerivationGradingFixed
public import ThirteenPlanes.Cartan.GradeRealDescent
public import ThirteenPlanes.SignedSupport

@[expose] public section

/-! Regrouping grades on a projective line and descent of a sum of stable summands. -/

namespace ThirteenPlanes.Cartan

noncomputable section

namespace NormalizedTernaryBasis

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

/-- The grades of a line group into its projective opposite-grade pairs. -/
theorem lineDerivations_eq_iSup_gradePairs (M : NormalizedTernaryBasis A) (l : SignedPlaneIndex) :
    M.lineDerivations (signedProjectiveLine l) =
      ⨆ p : {p : SignedPlaneIndex // signedPointOnLine p l}, M.gradePair p.val.val.val := by
  classical
  let L := signedProjectiveLine l
  let P := {p : SignedPlaneIndex // signedPointOnLine p l}
  change (⨆ g : L, M.derivationGrade g.val) = ⨆ p : P, M.gradePair p.val.val.val
  apply le_antisymm
  · apply iSup_le
    intro g
    by_cases hzero : g.val = 0
    · rw [hzero, M.derivationGrade_zero_eq_bot]
      exact bot_le
    by_cases hrep : isChargeRepresentative g.val
    · let p : P := ⟨⟨⟨g.val, hzero⟩, hrep⟩, g.property⟩
      exact (show M.derivationGrade g.val ≤ M.gradePair p.val.val.val from le_sup_left).trans
        (le_iSup (fun p : P => M.gradePair p.val.val.val) p)
    · let p : P := ⟨⟨⟨-g.val, neg_ne_zero.mpr hzero⟩,
        (oppositeCharge_isRepresentative_iff ⟨g.val, hzero⟩).mpr hrep⟩, L.neg_mem g.property⟩
      have h : M.derivationGrade g.val ≤ M.gradePair p.val.val.val := by
        change M.derivationGrade g.val ≤ M.derivationGrade (-g.val) ⊔ M.derivationGrade (- -g.val)
        rw [neg_neg]
        exact le_sup_right
      exact h.trans (le_iSup (fun p : P => M.gradePair p.val.val.val) p)
  · apply iSup_le
    intro p
    have hp : p.val.val.val ∈ L := p.property
    exact sup_le (le_iSup (fun g : L => M.derivationGrade g.val) ⟨p.val.val.val, hp⟩)
      (le_iSup (fun g : L => M.derivationGrade g.val) ⟨-p.val.val.val, L.neg_mem hp⟩)

end NormalizedTernaryBasis

namespace LieComplex

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K] {ι : Type*}

/-- A sum of conjugation-stable complex subalgebras descends to the sum of their real parts. -/
theorem iSup_toSubmodule_descend_eq (H : ι → LieSubalgebra ℂ (LieComplex K))
    (stable : ∀ i, Set.MapsTo conjugation (H i : Set (LieComplex K)) (H i : Set (LieComplex K))) :
    (⨆ i, (descend (H i)).toSubmodule) =
      ((⨆ i, (H i).toSubmodule).restrictScalars ℝ).comap ofReal.toLinearMap := by
  apply le_antisymm
  · apply iSup_le
    intro i x hx
    change ofReal x ∈ ⨆ j, (H j).toSubmodule
    exact Submodule.mem_iSup_of_mem i hx
  · intro x hx
    change ofReal x ∈ ⨆ i, (H i).toSubmodule at hx
    suffices h : realPart (ofReal x) ∈ ⨆ i, (descend (H i)).toSubmodule by simpa using h
    refine Submodule.iSup_induction _ (motive := fun z => realPart z ∈
      ⨆ i, (descend (H i)).toSubmodule) hx ?_ ?_ ?_
    · intro i z hz
      have hz' : z ∈ extend (descend (H i)) := by
        rw [extend_descend_of_stable _ (stable i)]
        exact hz
      exact Submodule.mem_iSup_of_mem i hz'.1
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

end LieComplex

end
end ThirteenPlanes.Cartan
