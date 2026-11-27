module

public import ThirteenPlanes.AlbertTriality.YokotaAction
public import ThirteenPlanes.AlbertTriality.FrameFixingSlots
public import ThirteenPlanes.AlbertTriality.TrialityOrientation

@[expose] public section

/-! The diagonal frame stabilizer on the native compact Albert algebra. -/

namespace ThirteenPlanes.AlbertTriality

open Glennie

noncomputable section

/-- Special orthogonality on each of the three literal octonion slots. -/
def YokotaSpecialOrthogonal (α : Fin 3 → OctEquiv) : Prop :=
  ∀ i, OctOrtho (α i) ∧ LinearMap.det (α i).toLinearMap = 1

/-- A real-linear equivalence of the actual compact Albert algebra preserves the
Jordan product and fixes each of the three diagonal atoms exactly when it has
the cyclic-slot formula for a special orthogonal Yokota triality triple. -/
/- The cyclic-slot characterization is the triality description in Ichiro Yokota,
Exceptional Lie Groups (arXiv:0902.0431), §1.16, Theorem 1.16.2, and Theorem 2.7.1.
The proof works on the native Albert algebra, with octonion conjugation on both sides
of the third component in the related-triple equation. -/
theorem diagonalFrameStabilizer_iff_yokotaTriality (e : Albert ≃ₗ[ℝ] Albert) :
    ((∀ x y, e (jordan x y) = jordan (e x) (e y)) ∧
      ∀ i, e (standardFrame i) = standardFrame i) ↔
    ∃ α : Fin 3 → OctEquiv,
      YokotaSpecialOrthogonal α ∧ YokotaRelated α ∧ YokotaSlotAction e α := by
  constructor
  · rintro ⟨he, hf⟩
    let α := frameFixing_slotAction e he hf
    have hs : ∀ i a, e (yokotaSlot i a) = yokotaSlot i (α i a) :=
      frameFixing_slotAction_apply e he hf
    have hO (i : Fin 3) : OctOrtho (α i) := frameFixing_slotAction_norm e he hf i
    have hr : YokotaRelated α := cyclicSlotMaps_relation e he α hs
    have hR : Related (α 0) (α 1) (octConjMap (α 2)) := hr
    obtain ⟨h0, h1, h2'⟩ := related_det_one (α 0) (α 1) (octConjMap (α 2))
      (hO 0) (hO 1) (octConjMap_ortho (hO 2)) hR
    have h2 : LinearMap.det (α 2).toLinearMap = 1 := (octConjMap_det (α 2)).symm.trans h2'
    refine ⟨α, ?_, hr, (yokotaSlotAction_iff e α).mpr ⟨hf, hs⟩⟩
    intro i
    refine ⟨hO i, ?_⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rintro ⟨α, hα, hr, ha⟩
    exact yokotaSlotAction_preserves_jordan e α (fun i => (hα i).1) hr ha

end
end ThirteenPlanes.AlbertTriality
