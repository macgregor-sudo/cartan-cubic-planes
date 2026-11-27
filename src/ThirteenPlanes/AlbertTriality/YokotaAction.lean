module

public import ThirteenPlanes.AlbertTriality.YokotaSlots
public import ThirteenPlanes.AlbertTriality.TrialityAction

@[expose] public section

/-! The exact cyclic-coordinate formula for the diagonal-frame stabilizer. -/

namespace ThirteenPlanes.AlbertTriality

open Glennie

noncomputable section

/-- These are exactly the matrices in Yokota's cyclic convention, including both
members of each conjugate pair. -/
theorem yokotaSlot_toMatrix (i : Fin 3) (a : Octonion) :
    toMatrix (yokotaSlot i a) =
      (![![![0, 0, 0], ![0, 0, a], ![0, octConj a, 0]],
          ![![0, 0, octConj a], ![0, 0, 0], ![a, 0, 0]],
          ![![0, a, 0], ![octConj a, 0, 0], ![0, 0, 0]]] :
        Fin 3 → Matrix (Fin 3) (Fin 3) Octonion) i := by
  apply Matrix.ext
  intro r c
  have hzero : octConj (0 : Octonion) = 0 := by simp [octConj]
  fin_cases i <;> fin_cases r <;> fin_cases c <;> simp [toMatrix, octScalar, hzero]

/-- The relatedness law on the three literal cyclic slot maps. -/
def YokotaRelated (α : Fin 3 → OctEquiv) : Prop :=
  ∀ a b, octMul (α 0 a) (α 1 b) = octConj (α 2 (octConj (octMul a b)))

/-- The printed action, tested on arbitrary diagonal and octonion coefficients. -/
def YokotaSlotAction (e : Albert ≃ₗ[ℝ] Albert) (α : Fin 3 → OctEquiv) : Prop :=
  ∀ (ξ : Fin 3 → ℝ) (a : Fin 3 → Octonion),
    e ((∑ i, ξ i • standardFrame i) + ∑ i, yokotaSlot i (a i)) =
      (∑ i, ξ i • standardFrame i) + ∑ i, yokotaSlot i (α i (a i))

theorem yokotaSlotAction_iff (e : Albert ≃ₗ[ℝ] Albert) (α : Fin 3 → OctEquiv) :
    YokotaSlotAction e α ↔
      (∀ i, e (standardFrame i) = standardFrame i) ∧
      ∀ i a, e (yokotaSlot i a) = yokotaSlot i (α i a) := by
  classical
  constructor
  · intro h
    constructor
    · intro i
      have hi := h (fun j => if j = i then 1 else 0) (fun _ => 0)
      simp only [map_zero, Finset.sum_const_zero, add_zero] at hi
      have hd : (∑ j : Fin 3, (if j = i then 1 else 0 : ℝ) • standardFrame j) =
          standardFrame i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      simpa only [hd] using hi
    · intro i a
      have hi := h (fun _ => 0) (fun j => if j = i then a else 0)
      simp only [zero_smul, Finset.sum_const_zero, zero_add] at hi
      have hd : (∑ j : Fin 3, yokotaSlot j (if j = i then a else 0)) =
          yokotaSlot i a := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      have hα : (∑ j : Fin 3, yokotaSlot j (α j (if j = i then a else 0))) =
          yokotaSlot i (α i a) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      simpa only [hd, hα] using hi
  · rintro ⟨hf, hs⟩ ξ a
    simp only [map_add, map_sum, map_smul, hf, hs]

theorem yokotaSlotAction_unique {e f : Albert ≃ₗ[ℝ] Albert}
    {α : Fin 3 → OctEquiv} (he : YokotaSlotAction e α) (hf : YokotaSlotAction f α) :
    e = f := by
  apply LinearEquiv.ext
  intro x
  obtain h := (he (fun i => diagonalCoordinateLinear i x) (fun i => yokotaSlotCoord i x)).trans
    (hf (fun i => diagonalCoordinateLinear i x) (fun i => yokotaSlotCoord i x)).symm
  rw [← albert_yokotaSlot_sum x] at h
  exact h

/-- Every norm-preserving cyclic related triple acts by an actual compact Albert automorphism. -/
theorem yokotaRelated_realize (α : Fin 3 → OctEquiv) (hα : ∀ i, OctOrtho (α i))
    (h : YokotaRelated α) :
    ∃ g : CompactAutomorphism, YokotaSlotAction g.equiv α := by
  have hrel : Related (α 0) (α 1) (octConjMap (α 2)) := h
  let g := relatedToCompactAuto (α 0) (α 1) (octConjMap (α 2))
    (hα 0) (hα 1) (octConjMap_ortho (hα 2)) hrel
  refine ⟨g, (yokotaSlotAction_iff _ _).mpr ⟨?_, ?_⟩⟩
  · intro i
    exact relatedToCompactAuto_fixes_frame _ _ _ _ _ _ _ i
  · intro i a
    change (relatedToCompactAuto _ _ _ _ _ _ _).equiv (yokotaSlot i a) = _
    rw [relatedToCompactAuto_apply]
    fin_cases i
    · simp [-octConjMap_apply]
    · simp [octConj_conj]
    · simp [-octConjMap_apply]

/-- The literal coordinate action of any norm-preserving cyclic triple with the
conjugated relation is a Jordan automorphism fixing all three diagonal atoms. -/
theorem yokotaSlotAction_preserves_jordan (e : Albert ≃ₗ[ℝ] Albert)
    (α : Fin 3 → OctEquiv) (hα : ∀ i, OctOrtho (α i)) (h : YokotaRelated α)
    (ha : YokotaSlotAction e α) :
    (∀ x y, e (jordan x y) = jordan (e x) (e y)) ∧
      ∀ i, e (standardFrame i) = standardFrame i := by
  obtain ⟨g, hg⟩ := yokotaRelated_realize α hα h
  rw [yokotaSlotAction_unique ha hg]
  exact ⟨g.map_jordan, (yokotaSlotAction_iff _ _).mp hg |>.1⟩

end
end ThirteenPlanes.AlbertTriality
