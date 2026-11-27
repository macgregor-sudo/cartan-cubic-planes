module

public import ThirteenPlanes.AlbertTriality.YokotaSlots

@[expose] public section

set_option backward.privateInPublic true

/-! The native Peirce projections and the cyclic slot actions of a diagonal frame fixer. -/

namespace ThirteenPlanes.AlbertTriality

open Glennie

noncomputable section

@[simp] private theorem octConj_zero : octConj (0 : Octonion) = 0 := by
  simp [octConj]

@[simp] private theorem octNormSq_zero : octNormSq (0 : Octonion) = 0 := by
  simp [octNormSq]

@[simp] private theorem octDot_zero_left (a : Octonion) : octDot 0 a = 0 := by
  simp [octDot_coordinates]

@[simp] private theorem octDot_zero_right (a : Octonion) : octDot a 0 = 0 := by
  simp [octDot_coordinates]

@[simp] private theorem octMul_zero_left (a : Octonion) : octMul 0 a = 0 := by
  simp [octMul]

@[simp] private theorem octMul_zero_right (a : Octonion) : octMul a 0 = 0 := by
  simp [octMul]

private theorem jordan_standardFrame_zero (x : Albert) :
    jordan (standardFrame 0) x =
      ⟨x.d0, 0, 0, (1 / 2 : ℝ) • x.o01, (1 / 2 : ℝ) • x.o02, 0⟩ := by
  apply Albert.ext <;> simp [standardFrame, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12]

private theorem jordan_standardFrame_one (x : Albert) :
    jordan (standardFrame 1) x =
      ⟨0, x.d1, 0, (1 / 2 : ℝ) • x.o01, 0, (1 / 2 : ℝ) • x.o12⟩ := by
  apply Albert.ext <;> simp [standardFrame, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12]

private theorem jordan_standardFrame_two (x : Albert) :
    jordan (standardFrame 2) x =
      ⟨0, 0, x.d2, 0, (1 / 2 : ℝ) • x.o02, (1 / 2 : ℝ) • x.o12⟩ := by
  apply Albert.ext <;> simp [standardFrame, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12]

/-- Project to a cyclic off-diagonal slot using the two incident diagonal atoms. -/
theorem yokotaSlot_peirce_projection (i : Fin 3) (x : Albert) :
    (4 : ℝ) • jordan (standardFrame (i + 1)) (jordan (standardFrame (i + 2)) x) =
      yokotaSlot i (yokotaSlotCoord i x) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · rw [show (0 + 1 : Fin 3) = 1 by decide, show (0 + 2 : Fin 3) = 2 by decide,
      jordan_standardFrame_one, jordan_standardFrame_two]
    apply Albert.ext <;> norm_num [smul_smul]
  · rw [show (1 + 1 : Fin 3) = 2 by decide, show (1 + 2 : Fin 3) = 0 by decide,
      jordan_standardFrame_two, jordan_standardFrame_zero]
    apply Albert.ext <;> norm_num [smul_smul]
  · rw [show (2 + 1 : Fin 3) = 0 by decide, show (2 + 2 : Fin 3) = 1 by decide,
      jordan_standardFrame_zero, jordan_standardFrame_one]
    apply Albert.ext <;> norm_num [smul_smul]

private theorem frameFixing_slot_mem
    (e : Albert ≃ₗ[ℝ] Albert)
    (he : ∀ x y, e (jordan x y) = jordan (e x) (e y))
    (hfix : ∀ i, e (standardFrame i) = standardFrame i)
    (i : Fin 3) (a : Octonion) :
    e (yokotaSlot i a) = yokotaSlot i (yokotaSlotCoord i (e (yokotaSlot i a))) := by
  calc
    e (yokotaSlot i a) =
        e ((4 : ℝ) • jordan (standardFrame (i + 1))
          (jordan (standardFrame (i + 2)) (yokotaSlot i a))) := by
        rw [yokotaSlot_peirce_projection, yokotaSlotCoord_slot]
    _ = (4 : ℝ) • jordan (standardFrame (i + 1))
          (jordan (standardFrame (i + 2)) (e (yokotaSlot i a))) := by
        rw [map_smul, he, he, hfix, hfix]
    _ = _ := yokotaSlot_peirce_projection i _

/-- Restrict a diagonal-frame-fixing Jordan automorphism to a literal cyclic slot. -/
def frameFixing_slotAction
    (e : Albert ≃ₗ[ℝ] Albert)
    (he : ∀ x y, e (jordan x y) = jordan (e x) (e y))
    (hfix : ∀ i, e (standardFrame i) = standardFrame i)
    (i : Fin 3) : Octonion ≃ₗ[ℝ] Octonion where
  toLinearMap := (yokotaSlotCoord i).comp (e.toLinearMap.comp (yokotaSlot i))
  invFun a := yokotaSlotCoord i (e.symm (yokotaSlot i a))
  left_inv a := by
    change yokotaSlotCoord i (e.symm
      (yokotaSlot i (yokotaSlotCoord i (e (yokotaSlot i a))))) = a
    rw [← frameFixing_slot_mem e he hfix, LinearEquiv.symm_apply_apply, yokotaSlotCoord_slot]
  right_inv a := by
    have hinv (x y : Albert) : e.symm (jordan x y) = jordan (e.symm x) (e.symm y) := by
      apply e.injective
      simp only [LinearEquiv.apply_symm_apply, he]
    have hfixInv (j : Fin 3) : e.symm (standardFrame j) = standardFrame j := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, hfix]
    change yokotaSlotCoord i (e
      (yokotaSlot i (yokotaSlotCoord i (e.symm (yokotaSlot i a))))) = a
    rw [← frameFixing_slot_mem e.symm hinv hfixInv, LinearEquiv.apply_symm_apply,
      yokotaSlotCoord_slot]

theorem frameFixing_slotAction_apply
    (e : Albert ≃ₗ[ℝ] Albert)
    (he : ∀ x y, e (jordan x y) = jordan (e x) (e y))
    (hfix : ∀ i, e (standardFrame i) = standardFrame i)
    (i : Fin 3) (a : Octonion) :
    e (yokotaSlot i a) = yokotaSlot i (frameFixing_slotAction e he hfix i a) :=
  frameFixing_slot_mem e he hfix i a

private theorem yokotaSlot_square (i : Fin 3) (a : Octonion) :
    jordan (yokotaSlot i a) (yokotaSlot i a) =
      octNormSq a • (standardFrame (i + 1) + standardFrame (i + 2)) := by
  fin_cases i
  · change jordan (yokotaSlot 0 a) (yokotaSlot 0 a) =
      octNormSq a • (standardFrame 1 + standardFrame 2)
    apply Albert.ext <;> norm_num [standardFrame, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12]
  · change jordan (yokotaSlot 1 a) (yokotaSlot 1 a) =
      octNormSq a • (standardFrame 2 + standardFrame 0)
    apply Albert.ext <;> norm_num [standardFrame, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12]
  · change jordan (yokotaSlot 2 a) (yokotaSlot 2 a) =
      octNormSq a • (standardFrame 0 + standardFrame 1)
    apply Albert.ext <;> norm_num [standardFrame, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12]

/-- The restricted equivalence is orthogonal for the native octonion norm. -/
theorem frameFixing_slotAction_norm
    (e : Albert ≃ₗ[ℝ] Albert)
    (he : ∀ x y, e (jordan x y) = jordan (e x) (e y))
    (hfix : ∀ i, e (standardFrame i) = standardFrame i)
    (i : Fin 3) (a : Octonion) :
    octNormSq (frameFixing_slotAction e he hfix i a) = octNormSq a := by
  have h := he (yokotaSlot i a) (yokotaSlot i a)
  rw [frameFixing_slotAction_apply e he hfix] at h
  simp only [yokotaSlot_square, map_smul, map_add, hfix] at h
  have hdiag : diagonalCoordinateLinear (i + 1)
      (standardFrame (i + 1) + standardFrame (i + 2)) = 1 := by
    fin_cases i
    · change diagonalCoordinateLinear 1 (standardFrame 1 + standardFrame 2) = 1
      simp [diagonalCoordinateLinear, standardFrame]
    · change diagonalCoordinateLinear 2 (standardFrame 2 + standardFrame 0) = 1
      simp [diagonalCoordinateLinear, standardFrame]
    · change diagonalCoordinateLinear 0 (standardFrame 0 + standardFrame 1) = 1
      simp [diagonalCoordinateLinear, standardFrame]
  have hc := congrArg (diagonalCoordinateLinear (i + 1)) h
  simpa only [map_smul, hdiag, smul_eq_mul, mul_one] using hc.symm

theorem frameFixing_slotAction_dot
    (e : Albert ≃ₗ[ℝ] Albert)
    (he : ∀ x y, e (jordan x y) = jordan (e x) (e y))
    (hfix : ∀ i, e (standardFrame i) = standardFrame i)
    (i : Fin 3) (a b : Octonion) :
    octDot (frameFixing_slotAction e he hfix i a) (frameFixing_slotAction e he hfix i b) =
      octDot a b :=
  octDot_of_norm_preserving _ (frameFixing_slotAction_norm e he hfix i) a b

end
end ThirteenPlanes.AlbertTriality
