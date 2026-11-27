module

public import Glennie.Diagonalization
public import Glennie.Automorphism

@[expose] public section

/-! Coordinate identities in the native compact Albert algebra for a diagonal first argument.

For diagonal `X` with diagonal entries `d₀,d₁,d₂` and any `Y`,
`⟨X², Y²⟩ - ⟨X∘Y, X∘Y⟩ = ½ ∑_{i<j} (dᵢ - dⱼ)² |Y_{ij}|²`. This is the Peirce form of
`⟨Y, (L_{X²} - L_X²) Y⟩`; no associativity of the octonions is used. -/

namespace ThirteenPlanes.AlbertGrading.CompletionO

open Glennie

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem octMul_zero_left (x : Octonion) : octMul 0 x = 0 := by
  apply Prod.ext <;> simp [octMul]

theorem octMul_zero_right (x : Octonion) : octMul x 0 = 0 := by
  apply Prod.ext <;> simp [octMul]

theorem octConj_zero : octConj (0 : Octonion) = 0 := by
  apply Prod.ext <;> simp [octConj]

theorem octDot_zero_left (x : Octonion) : octDot 0 x = 0 := by
  simp [octDot_coordinates]

theorem octDot_zero_right (x : Octonion) : octDot x 0 = 0 := by
  simp [octDot_coordinates]

theorem octNormSq_zero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl

theorem octDot_smul_right (r : ℝ) (x y : Octonion) : octDot x (r • y) = r * octDot x y := by
  rw [octDot_comm, octDot_smul_left, octDot_comm]

theorem octNormSq_smul (r : ℝ) (x : Octonion) : octNormSq (r • x) = r ^ 2 * octNormSq x := by
  rw [← octDot_self, ← octDot_self, octDot_smul_left, octDot_smul_right]
  ring

/-- The Peirce gap between `⟨X²,Y²⟩` and `|X∘Y|²` for diagonal `X`. -/
theorem diagonal_gap (X Y : Albert) (hX : IsDiagonal X) :
    inner (jordan X X) (jordan Y Y) - inner (jordan X Y) (jordan X Y) =
      ((X.d0 - X.d1) ^ 2 * octNormSq Y.o01 + (X.d0 - X.d2) ^ 2 * octNormSq Y.o02 +
        (X.d1 - X.d2) ^ 2 * octNormSq Y.o12) / 2 := by
  obtain ⟨h01, h02, h12⟩ := hX
  simp only [inner_coordinates, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02,
    jordan_o12, h01, h02, h12, octMul_zero_left, octMul_zero_right, octConj_zero, smul_zero,
    add_zero, zero_add]
  simp only [octDot_zero_left, octDot_zero_right, octDot_smul_left, octDot_smul_right,
    octDot_self, octNormSq_smul, octNormSq_zero, mul_zero, zero_mul, add_zero]
  ring

/-- Diagonal elements are combinations of the standard frame. -/
theorem diagonal_eq_sum (X : Albert) (hX : IsDiagonal X) :
    X = ∑ a, (![X.d0, X.d1, X.d2] : Fin 3 → ℝ) a • standardFrame a := by
  obtain ⟨h01, h02, h12⟩ := hX
  apply Albert.ext <;> simp [standardFrame, Fin.sum_univ_three, h01, h02, h12]

theorem standardFrame_two_jordan (Y : Albert) (h02 : Y.o02 = 0) (h12 : Y.o12 = 0) :
    jordan (standardFrame 2) Y = Y.d2 • standardFrame 2 := by
  apply Albert.ext <;>
    simp [standardFrame, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      h02, h12, octMul_zero_left, octMul_zero_right, octConj_zero, octDot_zero_left,
      octDot_zero_right, octNormSq_zero]

theorem standardFrame_one_jordan (Y : Albert) (h01 : Y.o01 = 0) (h12 : Y.o12 = 0) :
    jordan (standardFrame 1) Y = Y.d1 • standardFrame 1 := by
  apply Albert.ext <;>
    simp [standardFrame, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      h01, h12, octMul_zero_left, octMul_zero_right, octConj_zero, octDot_zero_left,
      octDot_zero_right, octNormSq_zero]

theorem standardFrame_zero_jordan (Y : Albert) (h01 : Y.o01 = 0) (h02 : Y.o02 = 0) :
    jordan (standardFrame 0) Y = Y.d0 • standardFrame 0 := by
  apply Albert.ext <;>
    simp [standardFrame, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      h01, h02, octMul_zero_left, octMul_zero_right, octConj_zero, octDot_zero_left,
      octDot_zero_right, octNormSq_zero]

theorem inner_self_diagonal (X : Albert) (hX : IsDiagonal X) :
    inner X X = X.d0 ^ 2 + X.d1 ^ 2 + X.d2 ^ 2 := by
  obtain ⟨h01, h02, h12⟩ := hX
  rw [inner_self_coordinates, h01, h02, h12]
  simp [octNormSq, Quaternion.normSq_def']

end

end ThirteenPlanes.AlbertGrading.CompletionO
