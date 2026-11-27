module

public import ThirteenPlanes.Quaternionic.Quartic
public import ThirteenPlanes.Quaternionic.Capacity
public import ThirteenPlanes.Quaternionic.PairProducts
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-! A joint quaternionic eigenbasis recovers a full frame plane.

A commuting traceless orthonormal pair spans the frame plane of the resulting two-sided
quaternionic basis. The result gives an equality of submodules in the native carrier. -/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma matrix_pair_range (X Y : QMat) :
    Set.range (![X, Y] : Fin 2 → QMat) = ({X, Y} : Set QMat) := by
  ext Z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · change X ∈ ({X, Y} : Set QMat)
      simp
    · change Y ∈ ({X, Y} : Set QMat)
      simp
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

lemma matrix_orthonormal_pair_linearIndependent (X Y : QMat)
    (hXX : traceForm X X = 1) (hYY : traceForm Y Y = 1)
    (hXY : traceForm X Y = 0) :
    LinearIndependent ℝ (![X, Y] : Fin 2 → QMat) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  rw [Fin.sum_univ_two] at hc
  change c 0 • X + c 1 • Y = 0 at hc
  have hYX : traceForm Y X = 0 := by rw [traceForm_comm, hXY]
  have hx := congrArg (fun A => traceForm A X) hc
  rw [traceForm_add_left, traceForm_smul_left, traceForm_smul_left, hXX, hYX] at hx
  norm_num [traceForm_eq_rtrace_mul] at hx
  have hy := congrArg (fun A => traceForm A Y) hc
  rw [traceForm_add_left, traceForm_smul_left, traceForm_smul_left, hXY, hYY] at hy
  norm_num [traceForm_eq_rtrace_mul] at hy
  fin_cases i
  · exact hx
  · exact hy

lemma matrix_orthonormal_pair_finrank (X Y : QMat)
    (hXX : traceForm X X = 1) (hYY : traceForm Y Y = 1)
    (hXY : traceForm X Y = 0) :
    Module.finrank ℝ (Submodule.span ℝ ({X, Y} : Set QMat)) = 2 := by
  rw [← matrix_pair_range X Y]
  simpa only [Fintype.card_fin] using
    _root_.finrank_span_eq_card (matrix_orthonormal_pair_linearIndependent X Y hXX hYY hXY)

lemma Frame.centered_span_eq_pair (F : Frame) :
    Submodule.span ℝ (Set.range F.centeredPointMatrix) =
      Submodule.span ℝ ({F.centeredPointMatrix 0, F.centeredPointMatrix 1} : Set QMat) := by
  classical
  let P := Submodule.span ℝ
    ({F.centeredPointMatrix 0, F.centeredPointMatrix 1} : Set QMat)
  have h0 : F.centeredPointMatrix 0 ∈ P := Submodule.subset_span (by simp)
  have h1 : F.centeredPointMatrix 1 ∈ P := Submodule.subset_span (by simp)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro Z ⟨a, rfl⟩
    fin_cases a
    · exact h0
    · exact h1
    · have hs := F.sum_centeredPointMatrix
      rw [Fin.sum_univ_three] at hs
      have h2 : F.centeredPointMatrix 2 =
          -(F.centeredPointMatrix 0 + F.centeredPointMatrix 1) :=
        eq_neg_of_add_eq_zero_right hs
      change F.centeredPointMatrix 2 ∈ P
      rw [h2]
      exact P.neg_mem (P.add_mem h0 h1)
  · apply Submodule.span_le.mpr
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with rfl | rfl
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩

lemma Frame.centered_span_finrank_le_two (F : Frame) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range F.centeredPointMatrix)) ≤ 2 := by
  rw [F.centered_span_eq_pair, ← matrix_pair_range]
  simpa only [Set.finrank, Fintype.card_fin] using
    (_root_.finrank_range_le_card
      (![F.centeredPointMatrix 0, F.centeredPointMatrix 1] : Fin 2 → QMat) (R := ℝ))

lemma QBasis.spectral_decomposition (U : QBasis) (A : QMat) (a : Outcome → ℝ)
    (hdiag : U.matᴴ * A * U.mat = realDiagonal a) :
    A = ∑ i, a i • U.point i := by
  calc
    A = U.mat * (U.matᴴ * A * U.mat) * U.matᴴ := by
      symm
      calc
        U.mat * (U.matᴴ * A * U.mat) * U.matᴴ =
            (U.mat * U.matᴴ) * A * (U.mat * U.matᴴ) := by simp only [mul_assoc]
        _ = A := by simp only [U.mul_adjoint, one_mul, mul_one]
    _ = U.mat * realDiagonal a * U.matᴴ := by rw [hdiag]
    _ = ∑ i, a i • U.point i := by
      apply Matrix.ext
      intro i j
      rw [Matrix.mul_apply]
      simp only [realDiagonal, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
        Matrix.sum_apply, Finset.sum_apply, QBasis.point, QBasis.column, projector, Matrix.smul_apply,
        Quaternion.mul_coe_eq_smul, smul_mul_assoc]

lemma QBasis.spectral_centered_decomposition (U : QBasis) (A : QMat) (a : Outcome → ℝ)
    (hdiag : U.matᴴ * A * U.mat = realDiagonal a) (ht : rtrace A = 0) :
    A = ∑ i, a i • U.toFrame.centeredPointMatrix i := by
  have ha : ∑ i, a i = 0 := by
    have h := rtrace_pow_eq_diagonal U A a hdiag 1
    simpa only [pow_one, ht] using h.symm
  have hs : (∑ i, a i • U.toFrame.centeredPointMatrix i) = ∑ i, a i • U.point i := by
    simp only [Frame.centeredPointMatrix, QBasis.toFrame_point, smul_sub, smul_smul,
      Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.sum_mul, ha,
      zero_mul, zero_smul, sub_zero]
  rw [hs]
  exact U.spectral_decomposition A a hdiag

/-- Every actual commuting orthonormal traceless Hermitian pair spans exactly
the centered projector plane of an actual quaternionic orthonormal basis. -/
theorem commuting_orthonormal_traceless_diagonal_plane
    (X Y : QMat) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (htX : rtrace X = 0) (htY : rtrace Y = 0)
    (hXX : traceForm X X = 1) (hYY : traceForm Y Y = 1)
    (hXY : traceForm X Y = 0) (hComm : Commute X Y) :
    ∃ U : QBasis,
      Submodule.span ℝ (Set.range U.toFrame.centeredPointMatrix) =
        Submodule.span ℝ ({X, Y} : Set QMat) := by
  obtain ⟨U, a, b, hdiagX, hdiagY⟩ :=
    commuting_hermitian_simultaneous_diagonalization X Y hX hY hComm
  let P := Submodule.span ℝ (Set.range U.toFrame.centeredPointMatrix)
  have hXm : X ∈ P := by
    rw [U.spectral_centered_decomposition X a hdiagX htX]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  have hYm : Y ∈ P := by
    rw [U.spectral_centered_decomposition Y b hdiagY htY]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  have hle : Submodule.span ℝ ({X, Y} : Set QMat) ≤ P := by
    apply Submodule.span_le.mpr
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with rfl | rfl
    · exact hXm
    · exact hYm
  have htarget := matrix_orthonormal_pair_finrank X Y hXX hYY hXY
  have hupper := U.toFrame.centered_span_finrank_le_two
  have hdim : Module.finrank ℝ (Submodule.span ℝ ({X, Y} : Set QMat)) =
      Module.finrank ℝ P := by
    apply le_antisymm
    · exact Submodule.finrank_mono hle
    · rw [htarget]
      exact hupper
  exact ⟨U, (Submodule.eq_of_le_of_finrank_eq hle hdim).symm⟩

end QuaternionicMUB
