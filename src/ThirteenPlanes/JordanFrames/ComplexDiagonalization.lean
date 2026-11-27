module

public import ThirteenPlanes.JordanFrames.Complex
public import Mathlib.Analysis.Matrix.Spectrum
public import QutritMutuallyUnbiasedBases

@[expose] public section

set_option backward.privateInPublic true

/-! Simultaneous diagonalization of the three idempotents of a complex matrix frame. -/

open scoped BigOperators Matrix

namespace ThirteenPlanes.JordanFrames

open RoundCubics AlbertSequential Unitary

noncomputable section

/-- Conjugation by an actual complex unitary matrix. -/
abbrev complexConjugate (U : Matrix.unitaryGroup (Fin 3) ℂ) :=
  Unitary.conjStarAlgAut ℂ ComplexMatrix3 U

theorem complexConjugate_trace (U : Matrix.unitaryGroup (Fin 3) ℂ) (X : ComplexMatrix3) :
    Matrix.trace (complexConjugate U X) = Matrix.trace X := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    show (star U : ComplexMatrix3) * U = 1 from Unitary.coe_star_mul_self U, one_mul]

theorem complexConjugate_inner (U : Matrix.unitaryGroup (Fin 3) ℂ) (X Y : ComplexMatrix3) :
    tracePairing (complexConjugate U X) (complexConjugate U Y) = tracePairing X Y := by
  change (Matrix.trace (complexConjugate U X * complexConjugate U Y)).re = _
  rw [← map_mul, complexConjugate_trace]
  rfl

theorem complexConjugate_jordan (U : Matrix.unitaryGroup (Fin 3) ℂ) (X Y : ComplexMatrix3) :
    complexConjugate U (symmetricMatrixProduct X Y) =
      symmetricMatrixProduct (complexConjugate U X) (complexConjugate U Y) := by
  simp only [symmetricMatrixProduct, map_smul, map_add, map_mul]

/-- The conjugated idempotents, still on the actual complex matrix carrier. -/
def conjugateComplexFrame (U : Matrix.unitaryGroup (Fin 3) ℂ) (F : ComplexTraceFrame3) :
    ComplexTraceFrame3 where
  point i := complexConjugate U (F.point i)
  hermitian i := by
    change star (complexConjugate U (F.point i)) = complexConjugate U (F.point i)
    rw [← map_star, show star (F.point i) = F.point i from (F.hermitian i).eq]
  trace_one i := (complexConjugate_trace U (F.point i)).trans (F.trace_one i)
  jordan_point i j := by
    rw [← complexConjugate_jordan, F.jordan_point]
    split_ifs <;> simp
  sum_unit := by
    change (∑ i, complexConjugate U (F.point i)) = 1
    rw [← map_sum, F.sum_unit, map_one]

theorem complex_framePoint_mul (F : ComplexTraceFrame3) (i j : Fin 3) :
    F.point i * F.point j = if i = j then F.point i else 0 := by
  have h (k : Fin 3) : F.point k * F.point k = F.point k := by
    have eq := F.jordan_point k k
    simp only [symmetricMatrixProduct, ← two_smul ℂ, smul_smul] at eq
    norm_num at eq
    exact eq
  by_cases hij : i = j
  · simpa [hij] using h j
  · rw [ite_eq_right hij]
    let P := F.point i
    let Q := F.point j
    have hp : P * P = P := h i
    have hab := F.jordan_point i j
    rw [ite_eq_right hij, symmetricMatrixProduct, smul_eq_zero] at hab
    have hsum : P * Q + Q * P = 0 :=
      hab.resolve_left (by norm_num)
    have hl := congrArg (P * ·) hsum
    rw [mul_add, mul_zero, ← mul_assoc P P Q, hp] at hl
    have hr := congrArg (· * P) hsum
    rw [add_mul, zero_mul, mul_assoc Q P P, hp, mul_assoc P Q P] at hr
    have he : P * Q = Q * P := by linear_combination (norm := abel) hl - hr
    rw [← he, ← two_smul ℂ, smul_eq_zero] at hsum
    exact hsum.resolve_left (by norm_num)

/-- The standard qutrit projectors are the three single-entry diagonal matrices. -/
theorem standardComplexPoint_diagonal (i : Fin 3) :
    AlbertSequential.qutritMUBProjection 0 i = Matrix.diagonal (Pi.single i (1 : ℂ)) := by
  ext a b
  change qutritStandardVector i a * star (qutritStandardVector i b) = _
  unfold qutritStandardVector
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, Pi.single_apply]
    split <;> simp
  · rw [Matrix.diagonal_apply_ne _ hab]
    by_cases hai : a = i
    · have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
      simp [Pi.single_apply, hbi]
    · simp [Pi.single_apply, hai]

private theorem diagPoint_mul (i j : Fin 3) :
    complexJordan (qutritMUBProjection 0 i) (qutritMUBProjection 0 j) =
      if i = j then qutritMUBProjection 0 i else 0 := by
  rw [complexJordan_apply, standardComplexPoint_diagonal, standardComplexPoint_diagonal,
    symmetricMatrixProduct, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst j
    ext a b
    by_cases hab : a = b
    · subst b
      by_cases hai : a = i <;>
        simp [Pi.single_apply, hai, Matrix.diagonal_apply_eq]
      norm_num
    · simp [hab]
  · ext a b
    by_cases hab : a = b
    · subst b
      by_cases hai : a = i
      · simp [Pi.single_apply, hai, hij]
      · simp [Pi.single_apply, hai, hij]
    · simp [hab, hij]

private theorem diagonal_mem_standardSpan (a : Fin 3 → ℂ) (ha : ∀ i, (a i).im = 0) :
    Matrix.diagonal a ∈ Submodule.span ℝ
      (Set.range (AlbertSequential.qutritMUBProjection 0)) := by
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨fun i => (a i).re, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.smul_apply, standardComplexPoint_diagonal,
      Matrix.diagonal_apply_eq, Pi.single_apply, Complex.real_smul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using (ha i).symm)
  · simp [Matrix.sum_apply, Matrix.smul_apply, standardComplexPoint_diagonal,
      Matrix.diagonal_apply_ne _ hij]

private theorem framePoint_diagonal_of_conjugate_difference (F : ComplexTraceFrame3)
    (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (d : Fin 3 → ℂ)
    (hd : complexConjugate U (F.point 2 - F.point 0) = Matrix.diagonal d) :
    ∀ i, ∃ a : Fin 3 → ℂ, complexConjugate U (F.point i) = Matrix.diagonal a := by
  let X := F.point 2 - F.point 0
  have h0 : F.point 0 = (1 / 2 : ℂ) • (X * X - X) := by
    simp only [X, sub_mul, mul_sub, complex_framePoint_mul]
    norm_num
    module
  have h2 : F.point 2 = (1 / 2 : ℂ) • (X * X + X) := by
    simp only [X, sub_mul, mul_sub, complex_framePoint_mul]
    norm_num
    module
  have h1 : F.point 1 = 1 - X * X := by
    have hs := F.sum_unit
    rw [Fin.sum_univ_three] at hs
    simp only [X, sub_mul, mul_sub, complex_framePoint_mul]
    norm_num
    linear_combination (norm := abel) hs
  have hd' : complexConjugate U X = Matrix.diagonal d := hd
  intro i
  fin_cases i
  · refine ⟨(1 / 2 : ℂ) • (d * d - d), ?_⟩
    change complexConjugate U (F.point 0) = _
    rw [h0, map_smul, map_sub, map_mul, hd', Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b <;> simp [hab, Matrix.smul_apply]
  · refine ⟨1 - d * d, ?_⟩
    change complexConjugate U (F.point 1) = _
    rw [h1, map_sub, map_one, map_mul, hd', Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b <;> simp [hab, Matrix.sub_apply]
  · refine ⟨(1 / 2 : ℂ) • (d * d + d), ?_⟩
    change complexConjugate U (F.point 2) = _
    rw [h2, map_smul, map_add, map_mul, hd', Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b <;> simp [hab, Matrix.smul_apply, mul_add]

set_option maxHeartbeats 800000 in
/-- A single unitary brings any complex matrix frame to the diagonal frame up to point order. -/
theorem complex_frame_to_diagonal (F : ComplexTraceFrame3) :
    ∃ (U : Matrix.unitaryGroup (Fin 3) ℂ) (σ : Equiv.Perm (Fin 3)),
      ∀ i, complexConjugate U (F.point i) = qutritMUBProjection 0 (σ i) := by
  let X := F.point 2 - F.point 0
  have hX : X.IsHermitian := (F.hermitian 2).sub (F.hermitian 0)
  let U := star hX.eigenvectorUnitary
  let G := conjugateComplexFrame U F
  have hdiag (i : Fin 3) : ∃ a : Fin 3 → ℂ, G.point i = Matrix.diagonal a :=
    framePoint_diagonal_of_conjugate_difference F U _ hX.conjStarAlgAut_star_eigenvectorUnitary i
  have h (i : Fin 3) : ∃ j, G.point i = qutritMUBProjection 0 j := by
    obtain ⟨a, ha⟩ := hdiag i
    have hreal (k : Fin 3) : (a k).im = 0 := by
      have hh := (G.hermitian i).eq
      rw [ha, Matrix.diagonal_conjTranspose] at hh
      have hk := congrArg (fun A : ComplexMatrix3 => (A k k).im) hh
      simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Complex.star_def, Complex.conj_im] at hk
      linarith
    have hspan : G.point i ∈ Submodule.span ℝ (Set.range (qutritMUBProjection 0)) :=
      ha.symm ▸ diagonal_mem_standardSpan a hreal
    apply eq_framePoint_of_mem_span complexJordan complexTrace
      (fun j => by
        change (Matrix.trace (qutritMUBProjection 0 j)).re = 1
        rw [qutritMUBProjection_trace, Complex.one_re]) diagPoint_mul hspan
    · change (Matrix.trace (G.point i)).re = 1
      rw [G.trace_one, Complex.one_re]
    · rw [complexJordan_apply, G.jordan_point, ite_eq_left rfl]
  choose σ hσ using h
  have hinj : Function.Injective σ := by
    intro i j e
    by_contra hn
    have hp : G.point i = G.point j := (hσ i).trans (e ▸ (hσ j).symm)
    have hz := G.jordan_point i j
    rw [← hp, G.jordan_point, ite_eq_left rfl, ite_eq_right hn] at hz
    have htr := G.trace_one i
    simp [hz] at htr
  exact ⟨U, Equiv.ofBijective σ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hσ⟩

end
end ThirteenPlanes.JordanFrames
