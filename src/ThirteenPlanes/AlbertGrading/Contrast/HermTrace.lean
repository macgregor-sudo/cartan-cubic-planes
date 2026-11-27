module

public import ThirteenPlanes.AlbertGrading.Contrast.Statements
public import Glennie.Diagonalization
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

set_option backward.privateInPublic true

/-!
# Traces on an embedded complex qutrit

The first step of the proof of the qutrit contrast table: three nonzero idempotents of `J` with sum `e` have
trace one (a consequence of (J2), proved here from the native diagonalization), so any
Jordan isomorphism `Herm₃(ℂ) → Q ⊆ J` onto a unital subalgebra preserves the unit and the trace.
-/

open scoped Matrix

namespace ThirteenPlanes.AlbertGrading.Contrast

noncomputable section

open Graded

/-- (J2): a nonzero idempotent of `J` has trace at least one. -/
theorem one_le_trace_of_idempotent (q : Glennie.Albert) (hq : Glennie.jordan q q = q)
    (hne : q ≠ 0) : 1 ≤ Glennie.trace q := by
  obtain ⟨g, h01, h02, h12⟩ := Glennie.native_diagonalization q
  have hdd : Glennie.jordan (g.equiv q) (g.equiv q) = g.equiv q := by rw [← g.map_jordan, hq]
  have e0 := congrArg Glennie.Albert.d0 hdd
  have e1 := congrArg Glennie.Albert.d1 hdd
  have e2 := congrArg Glennie.Albert.d2 hdd
  rw [Glennie.jordan_d0, h01, h02] at e0
  rw [Glennie.jordan_d1, h01, h12] at e1
  rw [Glennie.jordan_d2, h02, h12] at e2
  simp only [Glennie.octDot_self, Glennie.octNormSq, Prod.fst_zero, Prod.snd_zero,
    Quaternion.normSq.map_zero, add_zero] at e0 e1 e2
  have htr : Glennie.trace q = (g.equiv q).d0 + (g.equiv q).d1 + (g.equiv q).d2 := by
    rw [← g.map_trace q]; rfl
  have bit : ∀ t : ℝ, t * t = t → t = 0 ∨ t = 1 := fun t ht => by
    have : t * (t - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hd : g.equiv q ≠ 0 := fun h => hne (g.equiv.injective (by rw [h, map_zero]))
  rw [htr]
  rcases bit _ e0 with a | a <;> rcases bit _ e1 with b | b <;> rcases bit _ e2 with c | c <;>
    try (rw [a, b, c]; norm_num)
  exact absurd (Glennie.Albert.ext a b c h01 h02 h12) hd

/-- Three nonzero idempotents of `J` with sum `e` have trace one. -/
theorem trace_eq_one_of_partition (r : Fin 3 → Glennie.Albert)
    (hid : ∀ a, Glennie.jordan (r a) (r a) = r a) (hne : ∀ a, r a ≠ 0)
    (hsum : r 0 + r 1 + r 2 = 1) : ∀ a, Glennie.trace (r a) = 1 := by
  have h := congrArg Glennie.trace hsum
  simp only [Glennie.trace_add, Glennie.trace_unit] at h
  have h0 := one_le_trace_of_idempotent _ (hid 0) (hne 0)
  have h1 := one_le_trace_of_idempotent _ (hid 1) (hne 1)
  have h2 := one_le_trace_of_idempotent _ (hid 2) (hne 2)
  intro a
  fin_cases a <;> simp <;> linarith

theorem symmetricMatrixProduct_self (M : ComplexMatrix3) :
    symmetricMatrixProduct M M = M * M := by
  unfold symmetricMatrixProduct
  rw [← two_smul ℂ (M * M), smul_smul]
  norm_num

theorem symmetricMatrixProduct_one_left (M : ComplexMatrix3) : symmetricMatrixProduct 1 M = M := by
  unfold symmetricMatrixProduct
  rw [Matrix.one_mul, Matrix.mul_one, ← two_smul ℂ M, smul_smul]
  norm_num

private def diagUnit (a : Fin 3) : ComplexMatrix3 :=
  Matrix.diagonal fun i => if i = a then (1 : ℂ) else 0

private theorem diagUnit_mul (a : Fin 3) : diagUnit a * diagUnit a = diagUnit a := by
  unfold diagUnit
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

private theorem diagUnit_sum : diagUnit 0 + diagUnit 1 + diagUnit 2 = 1 := by
  unfold diagUnit
  rw [Matrix.diagonal_add, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem diagUnit_hermitian (a : Fin 3) : (diagUnit a).IsHermitian := by
  unfold diagUnit Matrix.IsHermitian
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i = a <;> simp [h]

private theorem diagUnit_trace (a : Fin 3) : Matrix.trace (diagUnit a) = 1 := by
  unfold diagUnit
  rw [Matrix.trace_diagonal]
  fin_cases a <;> simp [Fin.sum_univ_three]

/-- The spectral theorem on `Herm₃(ℂ)` in frame form (without orthogonality, which is not used). -/
theorem herm_spectral (X : FullHermitian3) :
    ∃ (R : Fin 3 → FullHermitian3) (lam : Fin 3 → ℝ),
      (∀ a, fullHermitianProduct (R a) (R a) = R a) ∧
      R 0 + R 1 + R 2 = ⟨1, Matrix.isHermitian_one⟩ ∧
      (∀ a, (Matrix.trace (R a).val).re = 1) ∧ X = ∑ a, lam a • R a := by
  have hX : X.val.IsHermitian := X.2
  set W := hX.eigenvectorUnitary
  have hW1 : star (W : ComplexMatrix3) * W = 1 := Unitary.star_mul_self_of_mem W.2
  have hW2 : (W : ComplexMatrix3) * star (W : ComplexMatrix3) = 1 :=
    Unitary.mul_star_self_of_mem W.2
  have hherm : ∀ a, ((W : ComplexMatrix3) * diagUnit a * star (W : ComplexMatrix3)).IsHermitian :=
    fun a => by
      rw [Matrix.star_eq_conjTranspose]
      exact Matrix.isHermitian_mul_mul_conjTranspose _ (diagUnit_hermitian a)
  let R : Fin 3 → FullHermitian3 := fun a => ⟨(W : ComplexMatrix3) * diagUnit a * star (W : ComplexMatrix3), hherm a⟩
  refine ⟨R, hX.eigenvalues, ?_, ?_, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    change symmetricMatrixProduct _ _ = _
    rw [symmetricMatrixProduct_self]
    calc (W : ComplexMatrix3) * diagUnit a * star (W : ComplexMatrix3) *
          ((W : ComplexMatrix3) * diagUnit a * star (W : ComplexMatrix3))
        = (W : ComplexMatrix3) * diagUnit a * (star (W : ComplexMatrix3) * W) * diagUnit a *
            star (W : ComplexMatrix3) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hW1, Matrix.mul_one, Matrix.mul_assoc (W : ComplexMatrix3) (diagUnit a) (diagUnit a),
          diagUnit_mul]
  · apply Subtype.ext
    change (W : ComplexMatrix3) * diagUnit 0 * star (W : ComplexMatrix3) +
      (W : ComplexMatrix3) * diagUnit 1 * star (W : ComplexMatrix3) +
      (W : ComplexMatrix3) * diagUnit 2 * star (W : ComplexMatrix3) = 1
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, diagUnit_sum,
      Matrix.mul_one, hW2]
  · intro a
    change (Matrix.trace ((W : ComplexMatrix3) * diagUnit a * star (W : ComplexMatrix3))).re = 1
    rw [Matrix.trace_mul_cycle, hW1, Matrix.one_mul, diagUnit_trace, Complex.one_re]
  · apply Subtype.ext
    have hs := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    change X.val = ∑ a, hX.eigenvalues a • ((W : ComplexMatrix3) * diagUnit a * star (W : ComplexMatrix3))
    refine hs.trans ?_
    have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) =
        ∑ a, hX.eigenvalues a • diagUnit a := by
      ext i j
      simp only [diagUnit, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hdiag, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]

/-- A Jordan isomorphism `Herm₃(ℂ) → Q` onto a unital subalgebra of `J` preserves the unit and
the trace. -/
theorem iso_unit_trace (Q : Submodule ℝ Glennie.Albert) (h1 : (1 : Glennie.Albert) ∈ Q)
    (I : FullHermitian3 ≃ₗ[ℝ] Q)
    (hI : ∀ X Y, (I (fullHermitianProduct X Y)).val = Glennie.jordan (I X).val (I Y).val) :
    (I ⟨1, Matrix.isHermitian_one⟩).val = 1 ∧
      ∀ X, Glennie.trace (I X).val = (Matrix.trace X.val).re := by
  have hunit : (I ⟨1, Matrix.isHermitian_one⟩).val = 1 := by
    set Y := I.symm ⟨1, h1⟩
    have hY : (I Y).val = 1 := by simp [Y]
    have h := hI ⟨1, Matrix.isHermitian_one⟩ Y
    have hp : fullHermitianProduct ⟨1, Matrix.isHermitian_one⟩ Y = Y :=
      Subtype.ext (symmetricMatrixProduct_one_left Y.val)
    rw [hp, hY, Glennie.jordan_unit_right] at h
    exact h.symm
  refine ⟨hunit, fun X => ?_⟩
  obtain ⟨R, lam, hid, hsum, htr, rfl⟩ := herm_spectral X
  have hne : ∀ a, (I (R a)).val ≠ 0 := by
    intro a h
    have h' : I (R a) = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at h'
    have := htr a
    rw [h'] at this
    simp at this
  have hone : ∀ a, Glennie.trace (I (R a)).val = 1 := by
    apply trace_eq_one_of_partition
    · intro a; rw [← hI, hid]
    · exact hne
    · rw [← Submodule.coe_add, ← Submodule.coe_add, ← map_add, ← map_add, hsum, hunit]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  rw [← Glennie.traceLinear_apply, map_sum]
  simp only [map_smul, Glennie.traceLinear_apply, hone, smul_eq_mul, mul_one]
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul, htr, mul_one]

end

end ThirteenPlanes.AlbertGrading.Contrast
