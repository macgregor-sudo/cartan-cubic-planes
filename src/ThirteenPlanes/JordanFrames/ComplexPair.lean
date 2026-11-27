module

public import ThirteenPlanes.JordanFrames.ComplexDiagonalization

@[expose] public section

set_option backward.privateInPublic true

/-! The diagonal and Fourier normal form for every unbiased pair of complex frames. -/

open scoped BigOperators Matrix

namespace ThirteenPlanes.JordanFrames

open RoundCubics AlbertSequential Unitary

noncomputable section

private theorem hermitian_entry (P : ComplexMatrix3) (h : P.IsHermitian) (i j : Fin 3) :
    star (P i j) = P j i := by
  exact congrArg (fun A : ComplexMatrix3 => A j i) h.eq

private theorem normSq_mul_star (x : ℂ) : x * star x = (Complex.normSq x : ℂ) := by
  rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

private theorem flat_norms (P : ComplexMatrix3) (hP : P.IsHermitian) (hPP : P * P = P)
    (hd : ∀ i, P i i = 1 / 3) :
    Complex.normSq (P 0 1) = 1 / 9 ∧ Complex.normSq (P 0 2) = 1 / 9 ∧
      Complex.normSq (P 1 2) = 1 / 9 := by
  have h (i : Fin 3) :
      ∑ j : Fin 3, (Complex.normSq (P i j) : ℂ) = P i i := by
    have hh := congrArg (fun A : ComplexMatrix3 => A i i) hPP
    change (∑ j, P i j * P j i) = P i i at hh
    calc
      _ = ∑ j, P i j * P j i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← (normSq_mul_star (P i j)), hermitian_entry P hP i j]
      _ = _ := hh
  have h₀ := congrArg Complex.re (h 0)
  have h₁ := congrArg Complex.re (h 1)
  have h₂ := congrArg Complex.re (h 2)
  simp only [Fin.sum_univ_three, ← hermitian_entry P hP 0 1, ← hermitian_entry P hP 0 2,
    ← hermitian_entry P hP 1 2, Complex.star_def, Complex.normSq_conj,
    Complex.add_re, Complex.ofReal_re, hd] at h₀ h₁ h₂
  have oneThird : Complex.normSq (1 / 3 : ℂ) = 1 / 9 := by
    norm_num [Complex.normSq, Complex.div_re, Complex.div_im]
  rw [oneThird] at h₀ h₁ h₂
  norm_num [Complex.div_re] at h₀ h₁ h₂
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem flat_slot_relation (P : ComplexMatrix3) (hPP : P * P = P)
    (hd : ∀ i, P i i = 1 / 3) : P 0 2 = 3 * P 0 1 * P 1 2 := by
  have h := congrArg (fun A : ComplexMatrix3 => A 0 2) hPP
  change (∑ i, P 0 i * P i 2) = P 0 2 at h
  rw [Fin.sum_univ_three, hd 0, hd 2] at h
  linear_combination -3 * h

private theorem tracePairing_standardPoint (A : ComplexMatrix3) (i : Fin 3) :
    tracePairing (qutritMUBProjection 0 i) A = (A i i).re := by
  simp only [tracePairing, standardComplexPoint_diagonal, Matrix.diagonal_mul, Matrix.trace,
    Matrix.diag_apply, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem frame_flat_of_unbiased_diagonal (G : ComplexTraceFrame3)
    (h : ∀ i j, tracePairing (qutritMUBProjection 0 i) (G.point j) = 1 / 3) :
    ∀ j i, G.point j i i = 1 / 3 := by
  intro j i
  apply Complex.ext
  · have h' := h i j
    rw [tracePairing_standardPoint] at h'
    simpa [Complex.div_re] using h'
  · have h' := congrArg Complex.im (hermitian_entry _ (G.hermitian j) i i)
    simp only [Complex.star_def, Complex.conj_im] at h'
    norm_num [Complex.div_im]
    linarith

private def normalizedComplexDiagonal (p : Fin 3 → ℂ) (hp : ∀ i, Complex.normSq (p i) = 1) :
    Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal p,
    Matrix.diagonal_mem_unitary.mpr (by
      rw [Unitary.mem_iff]
      constructor
      · funext i
        change star (p i) * p i = 1
        rw [mul_comm, normSq_mul_star, hp, Complex.ofReal_one]
      · funext i
        change p i * star (p i) = 1
        rw [normSq_mul_star, hp, Complex.ofReal_one])⟩

private theorem normalizedComplexDiagonal_apply (p : Fin 3 → ℂ)
    (hp : ∀ i, Complex.normSq (p i) = 1) (P : ComplexMatrix3) (i j : Fin 3) :
    complexConjugate (normalizedComplexDiagonal p hp) P i j = p i * P i j * star (p j) := by
  rw [Unitary.conjStarAlgAut_apply]
  change ((Matrix.diagonal p) * P * (Matrix.diagonal p)ᴴ) i j = _
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]

private theorem normalizedComplexDiagonal_fixes (p : Fin 3 → ℂ)
    (hp : ∀ i, Complex.normSq (p i) = 1) (i : Fin 3) :
    complexConjugate (normalizedComplexDiagonal p hp) (qutritMUBProjection 0 i) =
      qutritMUBProjection 0 i := by
  ext a b
  rw [normalizedComplexDiagonal_apply, standardComplexPoint_diagonal]
  by_cases h : a = b
  · subst b
    rw [Matrix.diagonal_apply_eq, Pi.single_apply]
    split
    · rw [mul_one, normSq_mul_star, hp, Complex.ofReal_one]
    · simp
  · simp [Matrix.diagonal_apply_ne _ h]

private def balancedComplexPoint : ComplexMatrix3 := fun _ _ => 1 / 3

private theorem complex_balanced_point (G : ComplexTraceFrame3)
    (h : ∀ j i, G.point j i i = 1 / 3) :
    ∃ D : Matrix.unitaryGroup (Fin 3) ℂ,
      (∀ i, complexConjugate D (qutritMUBProjection 0 i) = qutritMUBProjection 0 i) ∧
      complexConjugate D (G.point 0) = balancedComplexPoint := by
  let P := G.point 0
  have hP : P * P = P := by simpa [P] using complex_framePoint_mul G 0 0
  obtain ⟨n01, n02, _⟩ := flat_norms P (G.hermitian 0) hP (h 0)
  let p : Fin 3 → ℂ := ![1, 3 * P 0 1, 3 * P 0 2]
  have hp (i : Fin 3) : Complex.normSq (p i) = 1 := by
    fin_cases i
    · exact Complex.normSq_one
    · change Complex.normSq (3 * P 0 1) = 1
      rw [map_mul, n01]
      norm_num [Complex.normSq]
    · change Complex.normSq (3 * P 0 2) = 1
      rw [map_mul, n02]
      norm_num [Complex.normSq]
  let D := normalizedComplexDiagonal p hp
  let A := complexConjugate D P
  have hA : A.IsHermitian := (conjugateComplexFrame D G).hermitian 0
  have hAA : A * A = A := by rw [show A = complexConjugate D P from rfl, ← map_mul, hP]
  have hd (i : Fin 3) : A i i = 1 / 3 := by
    rw [show A = complexConjugate (normalizedComplexDiagonal p hp) P from rfl,
      normalizedComplexDiagonal_apply, show P i i = _ from h 0 i]
    calc
      _ = (1 / 3 : ℂ) * (p i * star (p i)) := by ring
      _ = (1 / 3 : ℂ) := by rw [normSq_mul_star, hp, Complex.ofReal_one, mul_one]
  have hEntry (i : Fin 3) (hi : i ≠ 0) (hn : Complex.normSq (P 0 i) = 1 / 9) :
      A 0 i = 1 / 3 := by
    have hpi : p i = 3 * P 0 i := by
      fin_cases i
      · exact (hi rfl).elim
      · rfl
      · rfl
    rw [show A = complexConjugate (normalizedComplexDiagonal p hp) P from rfl,
      normalizedComplexDiagonal_apply, show p 0 = 1 from rfl, hpi, one_mul, star_mul]
    rw [show star (3 : ℂ) = 3 by norm_num, ← mul_assoc, normSq_mul_star, hn]
    norm_num
  have h01 := hEntry 1 (by decide) n01
  have h02 := hEntry 2 (by decide) n02
  have h12 : A 1 2 = 1 / 3 := by
    have h' := flat_slot_relation A hAA hd
    rw [h01, h02] at h'
    linear_combination -h'
  refine ⟨D, normalizedComplexDiagonal_fixes p hp, ?_⟩
  change A = balancedComplexPoint
  ext i j
  fin_cases i <;> fin_cases j
  · exact hd 0
  · exact h01
  · exact h02
  · change A 1 0 = (1 / 3 : ℂ)
    rw [← hermitian_entry A hA 0 1, h01]
    norm_num [balancedComplexPoint]
  · exact hd 1
  · exact h12
  · change A 2 0 = (1 / 3 : ℂ)
    rw [← hermitian_entry A hA 0 2, h02]
    norm_num [balancedComplexPoint]
  · change A 2 1 = (1 / 3 : ℂ)
    rw [← hermitian_entry A hA 1 2, h12]
    norm_num [balancedComplexPoint]
  · exact hd 2

private def complexPhasePoint (x : ℂ) : ComplexMatrix3 :=
  !![1 / 3, x, star x; star x, 1 / 3, x; x, star x, 1 / 3]

private theorem qutrit_fourier_projection_zero :
    qutritMUBProjection 1 0 = balancedComplexPoint := by
  have hq (i : Fin 3) : qutritBasisVector 1 0 i = (Real.sqrt (1 / 3) : ℂ) := by
    change qutritFourierVector 1 0 i = _
    fin_cases i <;> simp [qutritFourierVector, qutritRawFourierVector, qutritCharacter]
  ext i j
  change qutritBasisVector 1 0 i * star (qutritBasisVector 1 0 j) = (1 / 3 : ℂ)
  rw [hq, hq, show star (Real.sqrt (1 / 3) : ℂ) = (Real.sqrt (1 / 3) : ℂ) by simp,
    qutritNormalization_square]

private theorem qutrit_fourier_projection_phase (k : Fin 3) (hk : k ≠ 0) :
    qutritMUBProjection 1 k = complexPhasePoint ((1 / 3 : ℂ) * star (qutritCharacter k)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  ext i j
  change qutritFourierVector 1 k i * star (qutritFourierVector 1 k j) = _
  set r : ℂ := (Real.sqrt (1 / 3) : ℂ)
  have hr : star r = r := by simp [r]
  have hrs : r * r = (1 / 3 : ℂ) := qutritNormalization_square
  change (r * qutritRawFourierVector 1 k i) * star (r * qutritRawFourierVector 1 k j) = _
  rw [star_mul, hr,
    show (r * qutritRawFourierVector 1 k i) * (star (qutritRawFourierVector 1 k j) * r) =
      (r * r) * (qutritRawFourierVector 1 k i * star (qutritRawFourierVector 1 k j)) by ring,
    hrs]
  fin_cases k
  · exact (hk rfl).elim
  all_goals
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [qutritRawFourierVector, complexPhasePoint, qutritCharacter,
        qutritRoot, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.div_im] <;> nlinarith

private theorem complex_flat_orthogonal_fourier (P : ComplexMatrix3)
    (hP : P.IsHermitian) (hPP : P * P = P) (hd : ∀ i, P i i = 1 / 3)
    (ho : P * balancedComplexPoint = 0) :
    ∃ k : Fin 3, k ≠ 0 ∧ P = qutritMUBProjection 1 k := by
  have hrows (i : Fin 3) : (P i 0 + P i 1 + P i 2) = 0 := by
    have h := congrArg (fun A : ComplexMatrix3 => A i 0) ho
    change (∑ j, P i j * (1 / 3 : ℂ)) = 0 at h
    rw [← Finset.sum_mul, mul_eq_zero, Fin.sum_univ_three] at h
    exact h.resolve_right (by norm_num)
  let x := P 0 1
  let y := P 1 2
  let z := P 0 2
  have h₀ : (1 / 3 : ℂ) + x + z = 0 := by simpa only [hd, x, z] using hrows 0
  have h₁ : star x + (1 / 3 : ℂ) + y = 0 := by
    simpa only [hd, x, y, hermitian_entry P hP 0 1] using hrows 1
  have h₂ : z + y + (1 / 3 : ℂ) = 0 := by
    have h := hrows 2
    simp only [hd, ← hermitian_entry P hP 0 2, ← hermitian_entry P hP 1 2] at h
    have h' := congrArg star h
    simpa only [star_add, star_star, star_div₀, star_one, star_ofNat, star_zero, z, y] using h'
  have hy : y = x := by linear_combination h₂ - h₀
  have hz : z = star x := by linear_combination h₀ - h₁ + hy
  have hx : x.re = -1 / 6 := by
    have hm := congrArg Complex.re h₁
    rw [hy] at hm
    norm_num [Complex.add_re, Complex.star_def, Complex.div_re] at hm
    linarith
  have hn : Complex.normSq x = 1 / 9 := (flat_norms P hP hPP hd).1
  have hi : x.im = Real.sqrt 3 / 6 ∨ x.im = -(Real.sqrt 3 / 6) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hq : (x.im - Real.sqrt 3 / 6) * (x.im + Real.sqrt 3 / 6) = 0 := by
      change x.re * x.re + x.im * x.im = 1 / 9 at hn
      rw [hx] at hn
      nlinarith
    exact (mul_eq_zero.mp hq).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left
  have hshape : P = complexPhasePoint x := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hd 0
    · rfl
    · exact hz
    · exact (hermitian_entry P hP 0 1).symm
    · exact hd 1
    · exact hy
    · change P 2 0 = x
      rw [← hermitian_entry P hP 0 2, show P 0 2 = star x from hz, star_star]
    · change P 2 1 = star x
      rw [← hermitian_entry P hP 1 2, show P 1 2 = x from hy]
    · exact hd 2
  have hChoice (k : Fin 3) (hk : k ≠ 0)
      (hk' : x = (1 / 3 : ℂ) * star (qutritCharacter k)) :
      ∃ k : Fin 3, k ≠ 0 ∧ P = qutritMUBProjection 1 k :=
    ⟨k, hk, by rw [hshape, hk', qutrit_fourier_projection_phase k hk]⟩
  rcases hi with hi | hi
  · apply hChoice 2 (by decide)
    apply Complex.ext <;>
      norm_num [hx, hi, qutritCharacter, qutritRoot, Complex.star_def, Complex.mul_re,
        Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring
  · apply hChoice 1 (by decide)
    apply Complex.ext <;>
      norm_num [hx, hi, qutritCharacter, qutritRoot, Complex.star_def, Complex.mul_re,
        Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

set_option maxHeartbeats 1000000 in
/-- A common unitary carries the two actual complex frames to the standard diagonal
frame and the Fourier frame, with independent outcome permutations. -/
theorem complex_normalize_unbiased_pair (F G : ComplexTraceFrame3)
    (h : ∀ i j, tracePairing (F.point i) (G.point j) = 1 / 3) :
    ∃ (U : Matrix.unitaryGroup (Fin 3) ℂ) (σ τ : Equiv.Perm (Fin 3)),
      (∀ i, complexConjugate U (F.point i) = qutritMUBProjection 0 (σ i)) ∧
      (∀ i, complexConjugate U (G.point i) = qutritMUBProjection 1 (τ i)) := by
  obtain ⟨U, σ, hU⟩ := complex_frame_to_diagonal F
  let G₀ := conjugateComplexFrame U G
  have hG₀ (i j : Fin 3) : tracePairing (qutritMUBProjection 0 i) (G₀.point j) = 1 / 3 := by
    rw [← σ.apply_symm_apply i, ← hU]
    change tracePairing (complexConjugate U (F.point (σ.symm i))) (complexConjugate U (G.point j)) = _
    rw [complexConjugate_inner]
    exact h (σ.symm i) j
  obtain ⟨D, hD, hD₀⟩ := complex_balanced_point G₀ (frame_flat_of_unbiased_diagonal G₀ hG₀)
  let H := conjugateComplexFrame (D * U) G
  have hFrame (i : Fin 3) : complexConjugate (D * U) (F.point i) = qutritMUBProjection 0 (σ i) := by
    rw [Unitary.conjStarAlgAut_mul_apply, hU, hD]
  have h₀ : H.point 0 = balancedComplexPoint := by
    change complexConjugate (D * U) (G.point 0) = _
    rw [Unitary.conjStarAlgAut_mul_apply]
    exact hD₀
  have h₁ (i j : Fin 3) : tracePairing (qutritMUBProjection 0 i) (H.point j) = 1 / 3 := by
    rw [← σ.apply_symm_apply i, ← hFrame]
    change tracePairing (complexConjugate (D * U) (F.point (σ.symm i))) (complexConjugate (D * U) (G.point j)) = _
    rw [complexConjugate_inner]
    exact h (σ.symm i) j
  have hmul := complex_framePoint_mul H 1 0
  rw [h₀] at hmul
  have hid := complex_framePoint_mul H 1 1
  obtain ⟨k, hk, hp⟩ := complex_flat_orthogonal_fourier (H.point 1) (H.hermitian 1)
    (by simpa using hid)
    (frame_flat_of_unbiased_diagonal H h₁ 1) (by simpa only [ite_eq_right (by decide : (1 : Fin 3) ≠ 0)] using hmul)
  have hzero : H.point 0 = qutritMUBProjection 1 0 := h₀.trans qutrit_fourier_projection_zero.symm
  have hlast (τ : Equiv.Perm (Fin 3)) (ht0 : τ 0 = 0) (ht1 : τ 1 = k) :
      ∀ i, H.point i = qutritMUBProjection 1 (τ i) := by
    have hsum : (∑ i, qutritMUBProjection 1 (τ i)) = 1 := by
      rw [Equiv.sum_comp, qutritMUBProjection_sum]
    have h₂ : H.point 2 = qutritMUBProjection 1 (τ 2) := by
      have hH := H.sum_unit
      rw [Fin.sum_univ_three, hzero, hp] at hH
      rw [Fin.sum_univ_three, ht0, ht1] at hsum
      exact add_left_cancel (hH.trans hsum.symm)
    intro i
    fin_cases i
    · exact hzero.trans (congrArg (qutritMUBProjection 1) ht0).symm
    · exact hp.trans (congrArg (qutritMUBProjection 1) ht1).symm
    · exact h₂
  have hk' : k = 1 ∨ k = 2 := by fin_cases k <;> first | contradiction | simp
  rcases hk' with rfl | rfl
  · exact ⟨D * U, σ, Equiv.refl _, hFrame, hlast _ rfl rfl⟩
  · exact ⟨D * U, σ, Equiv.swap 1 2, hFrame, hlast _ (by decide) (by decide)⟩

end
end ThirteenPlanes.JordanFrames
