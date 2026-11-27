module

public import Glennie.Diagonalization
public import Glennie.Compactness

@[expose] public section

set_option backward.privateInPublic true

/-! The three cyclic slots in Yokota's Hermitian matrix convention. -/

namespace ThirteenPlanes.AlbertTriality

open Glennie

noncomputable section

/-- The three cyclic entries, in the order `(1,2), (2,0), (0,1)` using zero-based indices. -/
def yokotaSlot (i : Fin 3) : Octonion →ₗ[ℝ] Albert where
  toFun a := ![(⟨0, 0, 0, 0, 0, a⟩ : Albert),
    ⟨0, 0, 0, 0, octConj a, 0⟩, ⟨0, 0, 0, a, 0, 0⟩] i
  map_add' a b := by
    fin_cases i <;> apply Albert.ext <;> simp [octConj_add]
  map_smul' r a := by
    fin_cases i <;> apply Albert.ext <;> simp [octConj_smul]

/-- Recover the actual cyclic entry of a native matrix. -/
def yokotaSlotCoord (i : Fin 3) : Albert →ₗ[ℝ] Octonion where
  toFun x := ![x.o12, octConj x.o02, x.o01] i
  map_add' x y := by fin_cases i <;> simp [octConj_add]
  map_smul' r x := by fin_cases i <;> simp [octConj_smul]

@[simp] theorem yokotaSlot_zero_apply (a : Octonion) :
    yokotaSlot 0 a = ⟨0, 0, 0, 0, 0, a⟩ := rfl

@[simp] theorem yokotaSlot_one_apply (a : Octonion) :
    yokotaSlot 1 a = ⟨0, 0, 0, 0, octConj a, 0⟩ := rfl

@[simp] theorem yokotaSlot_two_apply (a : Octonion) :
    yokotaSlot 2 a = ⟨0, 0, 0, a, 0, 0⟩ := rfl

@[simp] theorem yokotaSlotCoord_zero_apply (x : Albert) :
    yokotaSlotCoord 0 x = x.o12 := rfl

@[simp] theorem yokotaSlotCoord_one_apply (x : Albert) :
    yokotaSlotCoord 1 x = octConj x.o02 := rfl

@[simp] theorem yokotaSlotCoord_two_apply (x : Albert) :
    yokotaSlotCoord 2 x = x.o01 := rfl

@[simp] theorem yokotaSlotCoord_slot (i : Fin 3) (a : Octonion) :
    yokotaSlotCoord i (yokotaSlot i a) = a := by
  fin_cases i <;> simp [yokotaSlotCoord, yokotaSlot, octConj_conj]

theorem yokotaSlot_injective (i : Fin 3) : Function.Injective (yokotaSlot i) :=
  Function.LeftInverse.injective (yokotaSlotCoord_slot i)

theorem albert_yokotaSlot_sum (x : Albert) :
    x = (∑ i, diagonalCoordinateLinear i x • standardFrame i) +
      ∑ i, yokotaSlot i (yokotaSlotCoord i x) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  apply Albert.ext <;> simp [diagonalCoordinateLinear, standardFrame, octConj_conj]

@[simp] private theorem conjugate_zero : octConj (0 : Octonion) = 0 := by
  simp [octConj]

@[simp] private theorem normSq_zero : octNormSq (0 : Octonion) = 0 := by
  simp [octNormSq]

@[simp] private theorem octDot_left_zero (x : Octonion) : octDot 0 x = 0 := by
  simp [octDot_coordinates]

@[simp] private theorem octDot_right_zero (x : Octonion) : octDot x 0 = 0 := by
  simp [octDot_coordinates]

@[simp] private theorem octMul_left_zero (x : Octonion) : octMul 0 x = 0 := by
  simp [octMul]

@[simp] private theorem octMul_right_zero (x : Octonion) : octMul x 0 = 0 := by
  simp [octMul]

/-- The product of the first two cyclic slots uses the conjugate of their octonion product. -/
theorem yokotaSlotProduct12 (a b : Octonion) :
    (2 : ℝ) • jordan (yokotaSlot 0 a) (yokotaSlot 1 b) =
      yokotaSlot 2 (octConj (octMul a b)) := by
  have hc : octMul (octConj b) (octConj a) = octConj (octMul a b) :=
    (octConj_mul a b).symm
  apply Albert.ext <;> simp [jordan_d0, jordan_d1, jordan_d2, jordan_o01,
    jordan_o02, jordan_o12, hc, smul_smul]

/-- A product-preserving map acting on the literal cyclic slots must satisfy the
conjugated third-component relation. -/
theorem cyclicSlotMaps_relation
    (e : Albert ≃ₗ[ℝ] Albert)
    (he : ∀ x y, e (jordan x y) = jordan (e x) (e y))
    (α : Fin 3 → Octonion ≃ₗ[ℝ] Octonion)
    (hα : ∀ i a, e (yokotaSlot i a) = yokotaSlot i (α i a))
    (a b : Octonion) :
    octMul (α 0 a) (α 1 b) = octConj (α 2 (octConj (octMul a b))) := by
  have h := congrArg e (yokotaSlotProduct12 a b)
  rw [map_smul, he, hα, hα, yokotaSlotProduct12, hα] at h
  have hc := congrArg octConj (yokotaSlot_injective 2 h)
  simpa only [octConj_conj] using hc

end
end ThirteenPlanes.AlbertTriality
