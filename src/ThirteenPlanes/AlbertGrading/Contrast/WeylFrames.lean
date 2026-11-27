module

public import ThirteenPlanes.AlbertGrading.Contrast.FrameContrast

@[expose] public section

/-!
# The Weyl eigenframes and the Jordan product of the `D_v`

Matrix facts for qutrit contrast table, on matrices indexed by `𝔽₃ = ZMod 3` (the `weylMatrix`).
`zIdx` reads a `Fin 3`-indexed matrix with `ZMod 3` indices (the identity on entries).
-/

open scoped Matrix

namespace ThirteenPlanes.AlbertGrading.Contrast

noncomputable section

/-- Complex matrices indexed by `𝔽₃`. -/
abbrev ZMat := Matrix (ZMod 3) (ZMod 3) ℂ

/-- The same matrix with indices read in `ZMod 3`. -/
def zIdx (A : ComplexMatrix3) : ZMat := fun i j => A i j

theorem zIdx_mul (A B : ComplexMatrix3) : zIdx (A * B) = zIdx A * zIdx B := rfl
theorem zIdx_add (A B : ComplexMatrix3) : zIdx (A + B) = zIdx A + zIdx B := rfl
theorem zIdx_sub (A B : ComplexMatrix3) : zIdx (A - B) = zIdx A - zIdx B := rfl
theorem zIdx_smul (c : ℂ) (A : ComplexMatrix3) : zIdx (c • A) = c • zIdx A := rfl
theorem zIdx_star (A : ComplexMatrix3) : zIdx (star A) = star (zIdx A) := rfl
theorem zIdx_conjTranspose (A : ComplexMatrix3) : zIdx Aᴴ = (zIdx A)ᴴ := rfl
theorem zIdx_one : zIdx (1 : ComplexMatrix3) = 1 := rfl
theorem zIdx_zero : zIdx (0 : ComplexMatrix3) = 0 := rfl
theorem zIdx_injective : Function.Injective zIdx := fun _ _ h => h

/-- The symmetrized product `½(AB + BA)`. -/
def symZ (A B : ZMat) : ZMat := (1 / 2 : ℂ) • (A * B + B * A)

theorem symZ_smul (a b : ℂ) (A B : ZMat) : symZ (a • A) (b • B) = (a * b) • symZ A B := by
  unfold symZ
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
  congr 1 <;> congr 1 <;> ring

theorem symZ_expand (A B C D : ZMat) :
    symZ (A + Complex.I • B) (C + Complex.I • D) =
      symZ A C - symZ B D + Complex.I • (symZ A D + symZ B C) := by
  unfold symZ
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  linear_combination (norm := module) ((1 / 2 : ℂ) * Complex.I_sq) • (B * D + D * B)

theorem weylMatrix_zero : weylMatrix 0 = 1 := by
  ext i j
  simp [weylMatrix, Matrix.one_apply]

theorem phase_out_zero : chargePhase (outcome 0) = 1 := by
  change chargeRoot ^ 0 = 1; exact pow_zero _
theorem phase_out_one : chargePhase (outcome 1) = chargeRoot := by
  change chargeRoot ^ 1 = chargeRoot; exact pow_one _
theorem phase_out_two : chargePhase (outcome 2) = chargeRoot ^ 2 := rfl
theorem phase_negout_zero : chargePhase (-outcome 0) = 1 := by
  change chargeRoot ^ 0 = 1; exact pow_zero _
theorem phase_negout_one : chargePhase (-outcome 1) = chargeRoot ^ 2 := rfl
theorem phase_negout_two : chargePhase (-outcome 2) = chargeRoot := by
  change chargeRoot ^ 1 = chargeRoot; exact pow_one _
theorem phase_mnegout_zero : chargePhase (-1 * outcome 0) = 1 := by
  change chargeRoot ^ 0 = 1; exact pow_zero _
theorem phase_mnegout_one : chargePhase (-1 * outcome 1) = chargeRoot ^ 2 := rfl
theorem phase_mnegout_two : chargePhase (-1 * outcome 2) = chargeRoot := by
  change chargeRoot ^ 1 = chargeRoot; exact pow_one _

/-- The contrast of the eigenframe of `D_v` is `D_v`. -/
theorem weyl_contrast_one (v : WeylLabel) :
    ∑ b : Fin 3, chargePhase (outcome b) • weylEigenMatrix v (outcome b) = weylMatrix v := by
  simp only [weylEigenMatrix, Fin.sum_univ_three, phase_out_zero, phase_out_one, phase_out_two,
    phase_negout_zero, phase_negout_one, phase_negout_two]
  linear_combination (norm := module)
    ((1 / 3 : ℂ) * chargeRoot_quadratic) • (1 : ZMat) +
    ((2 / 3 : ℂ) * chargeRoot_cube) • weylMatrix v +
    ((1 / 3 : ℂ) * (chargeRoot ^ 2 - chargeRoot + 1) * chargeRoot_quadratic) • weylMatrix (-v)

/-- With conjugate characters the eigenframe of `D_v` gives `D_{-v} = D_v^*`. -/
theorem weyl_contrast_neg (v : WeylLabel) :
    ∑ b : Fin 3, chargePhase (-1 * outcome b) • weylEigenMatrix v (outcome b) = weylMatrix (-v) := by
  simp only [weylEigenMatrix, Fin.sum_univ_three, phase_mnegout_zero, phase_mnegout_one,
    phase_mnegout_two, phase_out_zero, phase_out_one, phase_out_two,
    phase_negout_zero, phase_negout_one, phase_negout_two]
  linear_combination (norm := module)
    ((1 / 3 : ℂ) * chargeRoot_quadratic) • (1 : ZMat) +
    ((1 / 3 : ℂ) * (chargeRoot ^ 2 - chargeRoot + 1) * chargeRoot_quadratic) • weylMatrix v +
    ((2 / 3 : ℂ) * chargeRoot_cube) • weylMatrix (-v)

theorem symplecticBracket_swap (v w : WeylLabel) :
    symplecticBracket w v = -symplecticBracket v w := by
  unfold symplecticBracket; ring

/-- `(5-weyl-jordan)`: `D_v ∘ D_w = D_{v+w}` for dependent and `-½ D_{v+w}` for independent `v, w`. -/
theorem weyl_sym (v w : WeylLabel) :
    symZ (weylMatrix v) (weylMatrix w) =
      (if symplecticBracket v w = 0 then (1 : ℂ) else -(1 / 2)) • weylMatrix (v + w) := by
  unfold symZ
  rw [weylMatrix_mul, weylMatrix_mul, symplecticBracket_swap v w, add_comm w v, ← add_smul,
    smul_smul]
  have hc := character_sum (symplecticBracket v w)
  congr 1
  split_ifs with h
  · rw [h, neg_zero, chargePhase_zero]; norm_num
  · rw [ite_eq_right h] at hc
    linear_combination (1 / 2 : ℂ) * hc

theorem dependent_iff (v w : WeylLabel) : Dependent v w ↔ symplecticBracket v w = 0 := by
  unfold Dependent symplecticBracket
  revert v w
  decide

theorem dependent_cases : ∀ v w : WeylLabel, Dependent v w → v = 0 ∨ w = 0 ∨ w = v ∨ w = -v := by
  unfold Dependent
  decide

theorem independent_ne : ∀ v w : WeylLabel, ¬ Dependent v w → v ≠ 0 ∧ w ≠ 0 ∧ v + w ≠ 0 := by
  unfold Dependent
  decide

theorem label_add_self : ∀ v : WeylLabel, v + v = -v := by decide

theorem label_eq_neg_self : ∀ v : WeylLabel, v = -v → v = 0 := by decide

theorem line_ne_zero : ∀ k : Fin 4, weylLinePoint k ≠ 0 := by decide

theorem line_cover : ∀ v : WeylLabel, v ≠ 0 → ∃ k : Fin 4, v = weylLinePoint k ∨ v = -weylLinePoint k := by
  decide

theorem line_unique : ∀ k l : Fin 4,
    (weylLinePoint k = weylLinePoint l ∨ weylLinePoint k = -weylLinePoint l) → k = l := by
  decide

end

end ThirteenPlanes.AlbertGrading.Contrast
