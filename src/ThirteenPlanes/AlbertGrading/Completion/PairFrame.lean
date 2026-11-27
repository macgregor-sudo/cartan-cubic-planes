module

public import ThirteenPlanes.AlbertGrading.Completion.Coordinates
public import ThirteenPlanes.NativeFrames

@[expose] public section

/-! Two orthonormal traceless Albert elements with `x² + y² = (2/3)e` lie in the span of one frame.

The round quartic identity
gives `⟨x²,y²⟩ = ⟨x∘y,x∘y⟩`. After the native diagonalization of `x` by an actual automorphism,
this difference is `½ ∑_{i<j} (λᵢ-λⱼ)² |y_{ij}|²`, so `y` has no entry between distinct eigenvalues
of `x`. If the eigenvalues are distinct, both elements are diagonal. If two coincide, the remaining
`2×2` block of `y` squares to half its unit and gives the frame explicitly. -/

namespace ThirteenPlanes.AlbertGrading.CompletionO

open Glennie
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- An explicit frame from a split idempotent block. -/
theorem frame_of_quarter (P T R : Albert)
    (hPP : jordan P P = P) (hPT : jordan P T = T) (hTT : jordan T T = (1 / 4 : ℝ) • P)
    (hRR : jordan R R = R) (hPR : jordan P R = 0) (hTR : jordan T R = 0)
    (hsum : P + R = 1) (htP : trace P = 2) (htT : trace T = 0) (htR : trace R = 1) :
    Frame ![(1 / 2 : ℝ) • P + T, (1 / 2 : ℝ) • P - T, R] := by
  have hTP : jordan T P = T := by rw [jordan_comm]; exact hPT
  have hRP : jordan R P = 0 := by rw [jordan_comm]; exact hPR
  have hRT : jordan R T = 0 := by rw [jordan_comm]; exact hTR
  have e00 : jordan ((1 / 2 : ℝ) • P + T) ((1 / 2 : ℝ) • P + T) = (1 / 2 : ℝ) • P + T := by
    simp only [jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
      hPP, hPT, hTP, hTT]
    module
  have e11 : jordan ((1 / 2 : ℝ) • P - T) ((1 / 2 : ℝ) • P - T) = (1 / 2 : ℝ) • P - T := by
    simp only [jordan_sub_left, jordan_sub_right, jordan_smul_left, jordan_smul_right,
      hPP, hPT, hTP, hTT]
    module
  have e01 : jordan ((1 / 2 : ℝ) • P + T) ((1 / 2 : ℝ) • P - T) = 0 := by
    simp only [jordan_add_left, jordan_sub_right, jordan_smul_left, jordan_smul_right,
      hPP, hPT, hTP, hTT]
    module
  have e02 : jordan ((1 / 2 : ℝ) • P + T) R = 0 := by
    simp only [jordan_add_left, jordan_smul_left, hPR, hTR]
    module
  have e12 : jordan ((1 / 2 : ℝ) • P - T) R = 0 := by
    simp only [jordan_sub_left, jordan_smul_left, hPR, hTR]
    module
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change trace ((1 / 2 : ℝ) • P + T) = 1
      rw [trace_add, trace_smul, htP, htT]; norm_num
    · change trace ((1 / 2 : ℝ) • P - T) = 1
      rw [trace_sub, trace_smul, htP, htT]; norm_num
    · exact htR
  · intro i
    fin_cases i
    · exact e00
    · exact e11
    · exact hRR
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact e01
    · exact e02
    · change jordan ((1 / 2 : ℝ) • P - T) ((1 / 2 : ℝ) • P + T) = 0
      rw [jordan_comm]; exact e01
    · exact (hij rfl).elim
    · exact e12
    · change jordan R ((1 / 2 : ℝ) • P + T) = 0
      rw [jordan_comm]; exact e02
    · change jordan R ((1 / 2 : ℝ) • P - T) = 0
      rw [jordan_comm]; exact e12
    · exact (hij rfl).elim
  · change (1 / 2 : ℝ) • P + T + ((1 / 2 : ℝ) • P - T) + R = 1
    rw [← hsum]
    module

/-- The coincident-eigenvalue case, in an arbitrary ordered frame. -/
theorem coincidence_common_frame (p : Fin 3 → Albert) (hp : Frame p) (X Y : Albert) (a : ℝ)
    (hX : X = a • p 0 + a • p 1 + (-2 * a) • p 2) (ha : 6 * a ^ 2 = 1)
    (hsq : jordan X X + jordan Y Y = (2 / 3 : ℝ) • (1 : Albert)) (c : ℝ)
    (hc : jordan (p 2) Y = c • p 2) (htY : trace Y = 0) :
    ∃ q : Fin 3 → Albert, Frame q ∧
      ∃ l m : Fin 3 → ℝ, X = ∑ b, l b • q b ∧ Y = ∑ b, m b • q b := by
  have e00 := hp.idempotent 0
  have e11 := hp.idempotent 1
  have e22 := hp.idempotent 2
  have e01 := hp.orthogonal 0 1 (by decide)
  have e02 := hp.orthogonal 0 2 (by decide)
  have e10 := hp.orthogonal 1 0 (by decide)
  have e12 := hp.orthogonal 1 2 (by decide)
  have e20 := hp.orthogonal 2 0 (by decide)
  have e21 := hp.orthogonal 2 1 (by decide)
  have hsum := hp.sum_unit
  have ha2 : a ^ 2 = 1 / 6 := by linarith
  have hXX : jordan X X = (1 / 6 : ℝ) • p 0 + (1 / 6 : ℝ) • p 1 + (2 / 3 : ℝ) • p 2 := by
    rw [hX]
    simp only [jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
      e00, e11, e22, e01, e02, e10, e12, e20, e21, smul_zero, add_zero, zero_add]
    have h1 : a * a = 1 / 6 := by nlinarith
    have h2 : -2 * a * (-2 * a) = 2 / 3 := by nlinarith
    rw [smul_smul, smul_smul, smul_smul, h1, h2]
  have hYY : jordan Y Y = (1 / 2 : ℝ) • p 0 + (1 / 2 : ℝ) • p 1 := by
    have h := eq_sub_of_add_eq' hsq
    rw [h, hXX, ← hsum]
    module
  have hc0 : c = 0 := by
    have h1 : inner (p 2) (jordan Y Y) = c * c := by
      rw [← inner_jordan_associative, hc, inner_smul_left]
      congr 1
      change trace (jordan (p 2) Y) = c
      rw [hc, trace_smul, hp.trace_one, mul_one]
    have h2 : inner (p 2) (jordan Y Y) = 0 := by
      rw [hYY, inner_add_right, inner_smul_right, inner_smul_right]
      simp only [Glennie.inner, e20, e21, trace_zero, mul_zero, add_zero]
    nlinarith
  rw [hc0, zero_smul] at hc
  set s : ℝ := Real.sqrt 2 / 2 with hs_def
  have hs2 : s ^ 2 = 1 / 2 := by
    rw [hs_def, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs2
    norm_num at hs2
  have hPdef : p 0 + p 1 = 1 - p 2 := eq_sub_of_add_eq hsum
  refine ⟨![(1 / 2 : ℝ) • (p 0 + p 1) + s • Y, (1 / 2 : ℝ) • (p 0 + p 1) - s • Y, p 2],
    frame_of_quarter (p 0 + p 1) (s • Y) (p 2) ?_ ?_ ?_ e22 ?_ ?_ hsum ?_ ?_ (hp.trace_one 2),
    ![a, a, -2 * a], ![1 / (2 * s), -(1 / (2 * s)), 0], ?_, ?_⟩
  · simp only [jordan_add_left, jordan_add_right, e00, e11, e01, e10]
    abel
  · rw [jordan_smul_right, hPdef, jordan_sub_left, jordan_unit_left, hc, sub_zero]
  · rw [jordan_smul_left, jordan_smul_right, hYY, smul_smul, ← pow_two, hs2]
    module
  · simp only [jordan_add_left, e02, e12, add_zero]
  · rw [jordan_smul_left, jordan_comm, hc, smul_zero]
  · rw [trace_add, hp.trace_one, hp.trace_one]; norm_num
  · rw [trace_smul, htY, mul_zero]
  · rw [hX, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    module
  · rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h : (1 / (2 * s)) • ((1 / 2 : ℝ) • (p 0 + p 1) + s • Y) +
        (-(1 / (2 * s))) • ((1 / 2 : ℝ) • (p 0 + p 1) - s • Y) + (0 : ℝ) • p 2 =
        (2 * (1 / (2 * s)) * s) • Y := by module
    rw [h, show 2 * (1 / (2 * s)) * s = 1 by field_simp, one_smul]

theorem frame_comp_perm (p : Fin 3 → Albert) (hp : Frame p) (σ : Equiv.Perm (Fin 3)) :
    Frame (p ∘ σ) where
  trace_one i := hp.trace_one (σ i)
  idempotent i := hp.idempotent (σ i)
  orthogonal i j hij := hp.orthogonal (σ i) (σ j) (σ.injective.ne hij)
  sum_unit := by
    have h := Equiv.sum_comp σ p
    simp only [Fin.sum_univ_three] at h
    simpa only [Function.comp_apply] using h.trans hp.sum_unit

theorem diagonal_eq_three (X : Albert) (hX : IsDiagonal X) :
    X = X.d0 • standardFrame 0 + X.d1 • standardFrame 1 + X.d2 • standardFrame 2 := by
  have h := diagonal_eq_sum X hX
  rw [Fin.sum_univ_three] at h
  simpa using h

/-- The coordinate case analysis after diagonalizing the first element. -/
theorem diag_common_frame (X Y : Albert) (hX : IsDiagonal X) (htx : trace X = 0)
    (hxx : inner X X = 1) (hty : trace Y = 0)
    (hsq : jordan X X + jordan Y Y = (2 / 3 : ℝ) • (1 : Albert))
    (hgap : inner (jordan X X) (jordan Y Y) = inner (jordan X Y) (jordan X Y)) :
    ∃ q : Fin 3 → Albert, Frame q ∧
      ∃ l m : Fin 3 → ℝ, X = ∑ b, l b • q b ∧ Y = ∑ b, m b • q b := by
  have hD := diagonal_gap X Y hX
  rw [hgap, sub_self] at hD
  have n01 := mul_nonneg (sq_nonneg (X.d0 - X.d1)) (octNormSq_nonneg Y.o01)
  have n02 := mul_nonneg (sq_nonneg (X.d0 - X.d2)) (octNormSq_nonneg Y.o02)
  have n12 := mul_nonneg (sq_nonneg (X.d1 - X.d2)) (octNormSq_nonneg Y.o12)
  have t01 : (X.d0 - X.d1) ^ 2 * octNormSq Y.o01 = 0 := by linarith
  have t02 : (X.d0 - X.d2) ^ 2 * octNormSq Y.o02 = 0 := by linarith
  have t12 : (X.d1 - X.d2) ^ 2 * octNormSq Y.o12 = 0 := by linarith
  have zero_of {u v : ℝ} {o : Octonion} (h : (u - v) ^ 2 * octNormSq o = 0) (huv : u ≠ v) :
      o = 0 :=
    (octNormSq_eq_zero o).mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr huv)))
  have htr : X.d0 + X.d1 + X.d2 = 0 := by simpa [trace] using htx
  have hn : X.d0 ^ 2 + X.d1 ^ 2 + X.d2 ^ 2 = 1 := by rw [← inner_self_diagonal X hX]; exact hxx
  have h3 := diagonal_eq_three X hX
  by_cases h01 : X.d0 = X.d1
  · have h02 : X.d0 ≠ X.d2 := by intro h; nlinarith
    have h12 : X.d1 ≠ X.d2 := h01 ▸ h02
    have o02 := zero_of t02 h02
    have o12 := zero_of t12 h12
    have hd2 : X.d2 = -2 * X.d0 := by linarith
    have ha : 6 * X.d0 ^ 2 = 1 := by rw [← h01, hd2] at hn; nlinarith [hn]
    refine coincidence_common_frame standardFrame standardFrame_isFrame X Y X.d0 ?_ ha
      hsq Y.d2 (standardFrame_two_jordan Y o02 o12) hty
    refine h3.trans ?_
    rw [← h01, hd2]
  · by_cases h02 : X.d0 = X.d2
    · have h12 : X.d1 ≠ X.d2 := fun h => h01 (h02.trans h.symm)
      have o01 := zero_of t01 h01
      have o12 := zero_of t12 h12
      have hd1 : X.d1 = -2 * X.d0 := by linarith
      have ha : 6 * X.d0 ^ 2 = 1 := by rw [← h02, hd1] at hn; nlinarith [hn]
      refine coincidence_common_frame (standardFrame ∘ Equiv.swap 1 2)
        (frame_comp_perm _ standardFrame_isFrame _) X Y X.d0 ?_ ha
        hsq Y.d1 ?_ hty
      · refine h3.trans ?_
        rw [← h02, hd1]
        simp only [Function.comp_apply]
        rw [show Equiv.swap (1 : Fin 3) 2 0 = 0 by decide, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
        abel
      · simp only [Function.comp_apply, Equiv.swap_apply_right]
        exact standardFrame_one_jordan Y o01 o12
    · by_cases h12 : X.d1 = X.d2
      · have o01 := zero_of t01 h01
        have o02 := zero_of t02 h02
        have hd0 : X.d0 = -2 * X.d1 := by linarith
        have ha : 6 * X.d1 ^ 2 = 1 := by rw [← h12, hd0] at hn; nlinarith [hn]
        refine coincidence_common_frame (standardFrame ∘ Equiv.swap 0 2)
          (frame_comp_perm _ standardFrame_isFrame _) X Y X.d1 ?_ ha
          hsq Y.d0 ?_ hty
        · refine h3.trans ?_
          rw [← h12, hd0]
          simp only [Function.comp_apply]
          rw [show Equiv.swap (0 : Fin 3) 2 1 = 1 by decide, Equiv.swap_apply_left,
            Equiv.swap_apply_right]
          abel
        · simp only [Function.comp_apply, Equiv.swap_apply_right]
          exact standardFrame_zero_jordan Y o01 o02
      · have hY : IsDiagonal Y := ⟨zero_of t01 h01, zero_of t02 h02, zero_of t12 h12⟩
        exact ⟨standardFrame, standardFrame_isFrame, _, _, diagonal_eq_sum X hX,
          diagonal_eq_sum Y hY⟩

end

end ThirteenPlanes.AlbertGrading.CompletionO
