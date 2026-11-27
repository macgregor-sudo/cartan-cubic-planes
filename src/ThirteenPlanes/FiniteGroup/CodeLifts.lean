module

public import ThirteenPlanes.FiniteGroup.Lifts

@[expose] public section

/-! Lifts of the special linear group of the ternary charges to symmetries of the signed cubic. -/

open Matrix

namespace ThirteenPlanes

noncomputable section

namespace FiniteGroup

/-- The relabeling of an odd phase function preserves the equal-strength cubic exactly when the phase
function satisfies the lifting condition on independent pairs. -/
theorem codeRelabeling_preserves_iff (A : SpecialLinearGroup (Fin 3) (ZMod 3))
    (F : Charge → ZMod 3) (hF : IsOddPhase F) :
    (codeRelabeling A F hF).PreservesCubic ↔ LiftCondition A F :=
  ((codeRelabeling A F hF).preservesCubic_iff).trans (tableInvariant_iff A F hF)

/-- Every determinant-one relabeling of the charges lifts, with an odd phase, to an isometry
preserving the equal-strength cubic. -/
theorem codeLift_exists (A : SpecialLinearGroup (Fin 3) (ZMod 3)) :
    ∃ (F : Charge → ZMod 3) (hF : IsOddPhase F), (codeRelabeling A F hF).PreservesCubic := by
  obtain ⟨F, hF, h⟩ := exists_lift A
  exact ⟨F, hF, (codeRelabeling_preserves_iff A F hF).mpr h⟩

/-- Two odd phase lifts of the same relabeling differ by a linear function. -/
theorem codeLift_unique (A : SpecialLinearGroup (Fin 3) (ZMod 3)) {F F' : Charge → ZMod 3}
    (hF : IsOddPhase F) (hF' : IsOddPhase F')
    (h : (codeRelabeling A F hF).PreservesCubic) (h' : (codeRelabeling A F' hF').PreservesCubic) :
    ∃ χ : Charge, ∀ x, F' x = F x + ∑ i, χ i * x i :=
  lift_unique hF hF' ((codeRelabeling_preserves_iff A F hF).mp h)
    ((codeRelabeling_preserves_iff A F' hF').mp h')

/-- A lift of the identity relabeling is one of the charge phase maps. -/
theorem codeLift_one_eq_chargeAction {F : Charge → ZMod 3} (hF : IsOddPhase F)
    (h : (codeRelabeling 1 F hF).PreservesCubic) :
    ∃ χ : Charge, (codeRelabeling 1 F hF).toIsometry = chargeAction χ := by
  have hz : IsOddPhase (fun _ : Charge => (0 : ZMod 3)) := fun _ => by simp
  have h0 : (codeRelabeling 1 (fun _ => 0) hz).PreservesCubic :=
    (codeRelabeling_preserves_iff 1 _ hz).mpr (fun x y _ => by simp)
  obtain ⟨χ, hχ⟩ := codeLift_unique 1 hz hF h0 h
  refine ⟨χ, ?_⟩
  ext X
  apply Subtype.ext
  funext y
  change Relabeling.coordMap _ (signedCoordinates X) y = signedCoordinates (chargeAction χ X) y
  change _ = signedCoordinates (chargeActionMap χ X) y
  rw [Relabeling.coordMap_apply, chargeActionMap_apply]
  have hy : (codeRelabeling 1 F hF).perm.symm y = y := by
    apply Subtype.ext
    change (((1 : SpecialLinearGroup (Fin 3) (ZMod 3))⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 3)) :
      ChargeMatrix) *ᵥ y.val = y.val
    simp
  rw [hy]
  change chargePhase (F y.val) * _ = _
  rw [hχ y.val, zero_add]
  congr 2

end FiniteGroup

end

end ThirteenPlanes
