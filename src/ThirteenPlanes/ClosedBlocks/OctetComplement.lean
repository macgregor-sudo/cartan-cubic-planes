module

public import ThirteenPlanes.ClosedBlocks.ScalarUnitary
public import ThirteenPlanes.Matrix3
public import FrameSlotNormalizers

@[expose] public section

set_option backward.privateInPublic true

/-! The matrix Gram bound in the standard Albert octet chart. -/

open scoped Matrix BigOperators

namespace ThirteenPlanes.ClosedBlocks

open AlbertSequential

noncomputable section

private def perpendicularToComplex (x : Octonion) : Prop :=
  x.1.re = 0 ∧ x.1.imI = 0

/-- Complex coordinates on the complement of the standard complex octonion line. -/
private def complexColumn (x : Octonion) : Fin 3 → ℂ :=
  ![⟨x.1.imJ, x.1.imK⟩, ⟨x.2.re, x.2.imI⟩, ⟨x.2.imJ, -x.2.imK⟩]

private def complexGram (x y : Octonion) : ℂ :=
  ∑ k : Fin 3, star (complexColumn x k) * complexColumn y k

private theorem complexGram_eq (x y : Octonion) (hx : perpendicularToComplex x)
    (hy : perpendicularToComplex y) :
    complexGram x y = ⟨-(octonionMul x y).1.re, (octonionMul x y).1.imI⟩ := by
  apply Complex.ext
  · simp [complexGram, complexColumn, Fin.sum_univ_three, Complex.mul_re, octonionMul, hx.1, hx.2, hy.1, hy.2]
    ring
  · simp [complexGram, complexColumn, Fin.sum_univ_three, Complex.mul_im, octonionMul, hx.1, hx.2, hy.1, hy.2]
    ring

private theorem complexGram_self (x : Octonion) (hx : perpendicularToComplex x) :
    complexGram x x = (octNormSq x : ℂ) := by
  apply Complex.ext
  · simp [complexGram, complexColumn, Fin.sum_univ_three, Complex.mul_re, octNormSq_eq_coords, hx.1, hx.2, pow_two]
    ring
  · simp [complexGram, complexColumn, Fin.sum_univ_three, Complex.mul_im]
    ring

private theorem complexColumn_inj {x y : Octonion} (hx : perpendicularToComplex x)
    (hy : perpendicularToComplex y) (h : complexColumn x = complexColumn y) : x = y := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  apply Prod.ext <;> apply Quaternion.ext
  · exact hx.1.trans hy.1.symm
  · exact hx.2.trans hy.2.symm
  · exact congrArg Complex.re h0
  · exact congrArg Complex.im h0
  · exact congrArg Complex.re h1
  · exact congrArg Complex.im h1
  · exact congrArg Complex.re h2
  · exact neg_injective (congrArg Complex.im h2)

theorem nativeOctonion_conj_eq_neg_of_real_zero {x : Octonion} (hx : x.1.re = 0) :
    octonionConj x = -x := by
  apply Prod.ext
  · change star x.1 = -x.1
    apply Quaternion.ext <;> simp [hx]
  · rfl

private def coordMatrix : Albert →ₗ[ℝ] ThirteenPlanes.ComplexMatrix3 where
  toFun x i j := complexColumn (x.2 j) i
  map_add' x y := Matrix.ext fun i j => by
    change complexColumn (x.2 j + y.2 j) i = complexColumn (x.2 j) i + complexColumn (y.2 j) i
    fin_cases i
    · rfl
    · rfl
    · apply Complex.ext
      · rfl
      · change -((x.2 j).2.imK + (y.2 j).2.imK) = -(x.2 j).2.imK + -(y.2 j).2.imK
        ring
  map_smul' t x := Matrix.ext fun i j => by
    change complexColumn (t • x.2 j) i = t • complexColumn (x.2 j) i
    have left : (t • x.2 j : Octonion).1 = t • (x.2 j).1 := rfl
    have right : (t • x.2 j : Octonion).2 = t • (x.2 j).2 := rfl
    apply Complex.ext <;> fin_cases i <;>
      simp [complexColumn, left, right, Complex.real_smul, smul_eq_mul]

private theorem coordMatrix_gram (x : Albert) (i j : Fin 3) :
    ((coordMatrix x)ᴴ * coordMatrix x) i j = complexGram (x.2 i) (x.2 j) := rfl

theorem nativeSquare_offDiagonal_of_zero_diagonal (x : Albert) (h : ∀ i, x.1 i = 0)
    (hc : ∀ i, (x.2 i).1.re = 0) :
    (jordanMul x x).2 0 = -(octonionMul (x.2 1) (x.2 2)) ∧
    (jordanMul x x).2 1 = octonionMul (x.2 0) (x.2 2) ∧
    (jordanMul x x).2 2 = -(octonionMul (x.2 0) (x.2 1)) := by
  rw [jordanMul_off_0, jordanMul_off_1, jordanMul_off_2,
    nativeOctonion_conj_eq_neg_of_real_zero (hc 2), nativeOctonion_conj_eq_neg_of_real_zero (hc 0),
    octonionMul_neg_left, octonionMul_neg_right]
  have half (v : Octonion) : (1 / 2 : ℝ) • (v + v) = v := by
    rw [← two_smul ℝ, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
  simp only [h, add_zero, zero_smul, zero_add, half, and_self]

private theorem gram_eq_scalar_of_components (x : Albert) (hd : ∀ i, x.1 i = 0)
    (hc : ∀ i, perpendicularToComplex (x.2 i))
    (hsquare_diag : ∀ i j : Fin 3, (jordanMul x x).1 i = (jordanMul x x).1 j)
    (hsquare_off : ∀ i : Fin 3, perpendicularToComplex ((jordanMul x x).2 i)) :
    (coordMatrix x)ᴴ * coordMatrix x = octNormSq (x.2 0) • (1 : ThirteenPlanes.ComplexMatrix3) := by
  have h0 := hsquare_diag 0 1
  have h1 := hsquare_diag 0 2
  simp only [jordanMul_diag_0, jordanMul_diag_1, jordanMul_diag_2, hd, zero_mul, octDot_self,
    zero_add] at h0 h1
  have hd1 : octNormSq (x.2 1) = octNormSq (x.2 0) := by linarith
  have hd2 : octNormSq (x.2 2) = octNormSq (x.2 0) := by linarith
  obtain ⟨hp0, hp1, hp2⟩ := nativeSquare_offDiagonal_of_zero_diagonal x hd (fun i => (hc i).1)
  have hGram01 : complexGram (x.2 0) (x.2 1) = 0 := by
    have h := hsquare_off 2
    rw [hp2] at h
    rw [complexGram_eq _ _ (hc 0) (hc 1)]
    apply Complex.ext
    · exact h.1
    · have hh : -(octonionMul (x.2 0) (x.2 1)).1.imI = 0 := h.2
      simpa only [Complex.zero_im, neg_eq_zero] using hh
  have hGram02 : complexGram (x.2 0) (x.2 2) = 0 := by
    have h := hsquare_off 1
    rw [hp1] at h
    rw [complexGram_eq _ _ (hc 0) (hc 2)]
    apply Complex.ext <;> simp [h.1, h.2]
  have hGram12 : complexGram (x.2 1) (x.2 2) = 0 := by
    have h := hsquare_off 0
    rw [hp0] at h
    rw [complexGram_eq _ _ (hc 1) (hc 2)]
    apply Complex.ext
    · exact h.1
    · have hh : -(octonionMul (x.2 1) (x.2 2)).1.imI = 0 := h.2
      simpa only [Complex.zero_im, neg_eq_zero] using hh
  have hGram_swap (u v : Octonion) : complexGram v u = star (complexGram u v) := by
    unfold complexGram
    rw [star_sum]
    congr 1
    ext k
    simp [mul_comm]
  ext i j
  change ((coordMatrix x)ᴴ * coordMatrix x) i j =
    (octNormSq (x.2 0) : ℂ) * (1 : ThirteenPlanes.ComplexMatrix3) i j
  rw [coordMatrix_gram]
  fin_cases i <;> fin_cases j
  · simp [complexGram_self _ (hc 0)]
  · simp [hGram01]
  · simp [hGram02]
  · simp [hGram_swap (x.2 0) (x.2 1), hGram01]
  · simp [complexGram_self _ (hc 1), hd1]
  · simp [hGram12]
  · simp [hGram_swap (x.2 0) (x.2 2), hGram02]
  · simp [hGram_swap (x.2 1) (x.2 2), hGram12]
  · simp [complexGram_self _ (hc 2), hd2]

private theorem diagonals_zero_of_ortho_window (x : Albert)
    (ho : ∀ y, standardComplexWindow.Contains y → AlbertSequential.tracePairing x y = 0) :
    ∀ i, x.1 i = 0 := by
  intro i
  have hi : standardComplexWindow.Contains (diagAtom i) := by
    rw [standardComplexWindow_contains_iff]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa only [tracePairing_comm x (diagAtom i), tracePairing_diagAtom] using ho _ hi

private theorem imaginary_of_ortho_window (x : Albert)
    (ho : ∀ y, standardComplexWindow.Contains y → AlbertSequential.tracePairing x y = 0) :
    ∀ i, perpendicularToComplex (x.2 i) := by
  intro i
  have h (z : ℂ) : octDot (x.2 i) (complexToOctonion z) = 0 := by
    have hz : standardComplexWindow.Contains (upperSlot i (complexToOctonion z)) := by
      rw [standardComplexWindow_contains_iff]
      fin_cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hh := ho _ hz
    rw [tracePairing_eq_coords] at hh
    fin_cases i <;> simp [upperSlot, octDot_zero_right] at hh <;> exact hh
  have hsmall (z : ℂ) : (x.2 i).1.re * z.re + (x.2 i).1.imI * z.im = 0 := by
    have hh := h z
    rw [octDot_eq_coords, complexToOctonion_apply] at hh
    simp only [show ((0 : Quaternion ℝ).re) = 0 from rfl,
      show ((0 : Quaternion ℝ).imI) = 0 from rfl, show ((0 : Quaternion ℝ).imJ) = 0 from rfl,
      show ((0 : Quaternion ℝ).imK) = 0 from rfl, mul_zero, add_zero] at hh
    exact hh
  exact ⟨by simpa using hsmall 1, by simpa using hsmall Complex.I⟩

/-- A real subspace orthogonal to the standard complex window and
closed under the centered Albert square has dimension at most two. -/
theorem standardOctetComplement_finrank_le_two (S : Submodule ℝ Albert)
    (orthogonal : ∀ x ∈ S, ∀ y, standardComplexWindow.Contains y → AlbertSequential.tracePairing x y = 0)
    (closedSquare : ∀ x ∈ S, jordanMul x x - (albertTrace (jordanMul x x) / 3) • albertUnit ∈ S) :
    Module.finrank ℝ S ≤ 2 := by
  have hd (x : S) := diagonals_zero_of_ortho_window x.val (orthogonal x.val x.property)
  have hc (x : S) := imaginary_of_ortho_window x.val (orthogonal x.val x.property)
  let F := coordMatrix.comp S.subtype
  have hF : Function.Injective F := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact (hd x i).trans (hd y i).symm
    · funext i
      apply complexColumn_inj (hc x i) (hc y i)
      funext j
      exact congrFun (congrFun he j) i
  have hGram : ∀ A ∈ F.range, ∃ t : ℝ, Aᴴ * A = t • (1 : ThirteenPlanes.ComplexMatrix3) := by
    rintro A ⟨x, rfl⟩
    let J := jordanMul x.val x.val
    let s := albertTrace J / 3
    let z : S := ⟨J - s • albertUnit, closedSquare x.val x.property⟩
    have he (i : Fin 3) : J.1 i = s := by
      have hi := hd z i
      change J.1 i - s * 1 = 0 at hi
      linarith
    have ho (i : Fin 3) : perpendicularToComplex (J.2 i) := by
      have hi := hc z i
      change perpendicularToComplex (J.2 i - s • (0 : Octonion)) at hi
      simpa only [smul_zero, sub_zero] using hi
    exact ⟨octNormSq (x.val.2 0), gram_eq_scalar_of_components x.val (hd x) (hc x)
      (fun i j => (he i).trans (he j).symm) ho⟩
  rw [← LinearMap.finrank_range_of_inj hF]
  exact scalarUnitarySubspace_finrank_le_two F.range hGram

end

end ThirteenPlanes.ClosedBlocks
