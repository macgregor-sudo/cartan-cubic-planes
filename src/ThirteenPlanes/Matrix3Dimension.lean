/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Matrix3Metric
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FinCases

/-! A coordinate bound for the dimension of the traceless Hermitian carrier. -/

@[expose] public section
noncomputable section

namespace ThirteenPlanes.TracelessHermitian3

open scoped Matrix

def independentEntries : TracelessHermitian3 →ₗ[ℝ] (Fin 2 → ℝ) × (Fin 3 → ℂ) where
  toFun x := (![ (toMatrix x 0 0).re, (toMatrix x 1 1).re ],
    ![toMatrix x 0 1, toMatrix x 0 2, toMatrix x 1 2])
  map_add' x y := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  map_smul' r x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp

theorem matrix_entry_conj (x : TracelessHermitian3) (i j : Fin 3) :
    star (toMatrix x i j) = toMatrix x j i :=
  congrFun (congrFun x.isHermitian.eq j) i

theorem matrix_diag_im (x : TracelessHermitian3) (i : Fin 3) : (toMatrix x i i).im = 0 := by
  have h := congrArg Complex.im (matrix_entry_conj x i i)
  change -(toMatrix x i i).im = (toMatrix x i i).im at h
  linarith

theorem independentEntries_injective : Function.Injective independentEntries := by
  intro x y h
  have h00re : (toMatrix x 0 0).re = (toMatrix y 0 0).re :=
    congrFun (congrArg Prod.fst h) 0
  have h11re : (toMatrix x 1 1).re = (toMatrix y 1 1).re :=
    congrFun (congrArg Prod.fst h) 1
  have h00 : toMatrix x 0 0 = toMatrix y 0 0 :=
    Complex.ext h00re (by rw [matrix_diag_im, matrix_diag_im])
  have h11 : toMatrix x 1 1 = toMatrix y 1 1 :=
    Complex.ext h11re (by rw [matrix_diag_im, matrix_diag_im])
  have h01 : toMatrix x 0 1 = toMatrix y 0 1 := congrFun (congrArg Prod.snd h) 0
  have h02 : toMatrix x 0 2 = toMatrix y 0 2 := congrFun (congrArg Prod.snd h) 1
  have h12 : toMatrix x 1 2 = toMatrix y 1 2 := congrFun (congrArg Prod.snd h) 2
  have h22 : toMatrix x 2 2 = toMatrix y 2 2 := by
    have hx := x.trace_eq_zero
    have hy := y.trace_eq_zero
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three, h00, h11] at hx hy
    linear_combination hx - hy
  have h10 : toMatrix x 1 0 = toMatrix y 1 0 := by
    rw [← matrix_entry_conj x, ← matrix_entry_conj y, h01]
  have h20 : toMatrix x 2 0 = toMatrix y 2 0 := by
    rw [← matrix_entry_conj x, ← matrix_entry_conj y, h02]
  have h21 : toMatrix x 2 1 = toMatrix y 2 1 := by
    rw [← matrix_entry_conj x, ← matrix_entry_conj y, h12]
  apply toMatrix_injective
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem finrank_le_eight : Module.finrank ℝ TracelessHermitian3 ≤ 8 := by
  have h := LinearMap.finrank_le_finrank_of_injective independentEntries_injective
  simpa [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex] using h

end ThirteenPlanes.TracelessHermitian3
