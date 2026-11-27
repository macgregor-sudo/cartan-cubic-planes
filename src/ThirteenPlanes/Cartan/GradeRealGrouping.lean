module

public import ThirteenPlanes.SignedPlanes
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

set_option backward.privateInPublic true

/-! Pairing the nonzero ternary grades and restricting the split to a faithful carrier. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An independent family spanning the image of an injective map gives an internal split
on the actual domain of that map. -/
theorem isInternal_comap_of_range {ι : Type*} [DecidableEq ι] (P : ι → Submodule ℂ W)
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hI : iSupIndep P)
    (hP : (⨆ i, P i) = f.range) :
    DirectSum.IsInternal (fun i => (P i).comap f) := by
  have him (i : ι) : ((P i).comap f).map f = P i :=
    Submodule.map_comap_eq_of_le ((le_iSup P i).trans_eq hP)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro i
    apply Submodule.disjoint_def.mpr
    intro x hxi hx
    apply hf
    rw [map_zero]
    refine (Submodule.disjoint_def.mp ((iSupIndep_def.mp hI) i)) _ hxi ?_
    have h := Submodule.mem_map_of_mem (f := f) hx
    simpa only [Submodule.map_iSup, him] using h
  · apply Submodule.map_injective_of_injective hf
    rw [Submodule.map_iSup, Submodule.map_top, hP.symm]
    simp only [him]

/-- The sum of the opposite complex degrees indexed by one projective plane. -/
def pairedGrade (U : Charge → Submodule ℂ V) (p : SignedPlaneIndex) : Submodule ℂ V :=
  U p.val.val ⊔ U (-p.val.val)

private theorem gradePair_as_iSup (U : Charge → Submodule ℂ V) (p : SignedPlaneIndex) :
    pairedGrade U p = ⨆ b : Bool, U (signedPlaneGradeEquiv (p, b)).val := by
  apply le_antisymm
  · apply sup_le
    · exact le_iSup (fun b => U (signedPlaneGradeEquiv (p, b)).val) false
    · exact le_iSup (fun b => U (signedPlaneGradeEquiv (p, b)).val) true
  · refine iSup_le fun b => ?_
    cases b
    · exact le_sup_left
    · exact le_sup_right

private theorem opposite_pair_index_injective :
    Function.Injective (fun b : SignedPlaneIndex × Bool => (signedPlaneGradeEquiv b).val) :=
  Subtype.val_injective.comp signedPlaneGradeEquiv.injective

/-- Grouping the independent nonzero grades into their disjoint opposite pairs preserves
independence. A zero degree equal to bottom then gives an internal split of the whole carrier. -/
theorem pairedGrade_isInternal (U : Charge → Submodule ℂ V)
    (hU : DirectSum.IsInternal U) (hz : U 0 = ⊥) :
    DirectSum.IsInternal (pairedGrade U) := by
  classical
  let F (v : SignedPlaneIndex × Bool) := U (signedPlaneGradeEquiv v).val
  have hI : iSupIndep F := hU.submodule_iSupIndep.comp opposite_pair_index_injective
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro p
    let same : Set (SignedPlaneIndex × Bool) := {v | v.1 = p}
    let other : Set (SignedPlaneIndex × Bool) := {v | v.1 ≠ p}
    have hdisj : Disjoint same other := by
      rw [Set.disjoint_left]
      intro v hv hnv
      exact hnv hv
    have hsame : pairedGrade U p ≤ ⨆ v ∈ same, F v := by
      rw [gradePair_as_iSup]
      exact iSup_le fun b => (le_iSup (fun v => ⨆ _ : v ∈ same, F v) (p, b)).trans'
        (le_iSup (fun _ : (p, b) ∈ same => F (p, b)) rfl)
    have hother : (⨆ q : SignedPlaneIndex, ⨆ _ : q ≠ p, pairedGrade U q) ≤
        ⨆ v ∈ other, F v := by
      refine iSup_le fun q => iSup_le fun hq => ?_
      rw [gradePair_as_iSup]
      exact iSup_le fun b => (le_iSup (fun v => ⨆ _ : v ∈ other, F v) (q, b)).trans'
        (le_iSup (fun _ : (q, b) ∈ other => F (q, b)) hq)
    exact (hI.disjoint_biSup_biSup hdisj).mono hsame hother
  · rw [← hU.submodule_iSup_eq_top]
    apply le_antisymm (le_top.trans_eq hU.submodule_iSup_eq_top.symm)
    refine iSup_le fun g => ?_
    by_cases hg : g = 0
    · rw [hg, hz]
      exact bot_le
    · obtain ⟨⟨p, b⟩, hb⟩ := signedPlaneGradeEquiv.surjective ⟨g, hg⟩
      have he : (signedPlaneGradeEquiv (p, b)).val = g := congrArg Subtype.val hb
      rw [← he]
      exact (le_iSup (fun e : Bool => U (signedPlaneGradeEquiv (p, e)).val) b).trans
        ((gradePair_as_iSup U p).ge.trans (le_iSup (pairedGrade U) p))

theorem pairedGrade_finrank (U : Charge → Submodule ℂ V) [Module.Finite ℂ V]
    (hU : iSupIndep U) (p : SignedPlaneIndex) :
    Module.finrank ℂ (pairedGrade U p) =
      Module.finrank ℂ (U p.val.val) + Module.finrank ℂ (U (-p.val.val)) := by
  have hrep := p.property
  have hopp := oppositeCharge_isRepresentative_iff p.val
  have hn : p.val.val ≠ -p.val.val := by
    intro h
    apply (hopp.mp ?_) hrep
    change isChargeRepresentative (-p.val.val)
    rwa [← h]
  have hd : Disjoint (U p.val.val) (U (-p.val.val)) := hU.pairwiseDisjoint hn
  have h := Submodule.finrank_sup_add_finrank_inf_eq (U p.val.val) (U (-p.val.val))
  change Module.finrank ℂ ↥(U p.val.val ⊔ U (-p.val.val)) = _
  rw [hd.eq_bot, finrank_bot, add_zero] at h
  exact h

/-- Different representatives specify disjoint opposite-charge sets. -/
theorem representatives_not_eq_or_neg {p q : SignedPlaneIndex} (hne : p ≠ q) :
    p.val.val ≠ q.val.val ∧ p.val.val ≠ -q.val.val := by
  refine ⟨fun h => hne (Subtype.ext (Subtype.ext h)), ?_⟩
  intro h
  have hrep : isChargeRepresentative (oppositeCharge q.val).val := by
    change isChargeRepresentative (-q.val.val)
    rw [← h]
    exact p.property
  exact (oppositeCharge_isRepresentative_iff q.val).mp hrep q.property

end

end ThirteenPlanes.Cartan
