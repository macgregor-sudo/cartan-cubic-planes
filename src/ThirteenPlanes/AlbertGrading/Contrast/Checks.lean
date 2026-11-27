module

public import ThirteenPlanes.AlbertGrading.Contrast.QutritTable

@[expose] public section

set_option backward.privateInPublic true

/-! Examples for the qutrit contrast table.

The four Weyl eigenframes in `Herm₃(ℂ)` are pairwise unbiased. A graded line algebra supplies
a complex Hermitian copy containing four native Albert frames with these hypotheses. -/

open scoped Matrix

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Contrast Contrast.AlbertC Graded

namespace Contrast

private theorem weyl_sq (v : WeylLabel) : weylMatrix v * weylMatrix v = weylMatrix (-v) := by
  rw [weylMatrix_mul, show symplecticBracket v v = 0 by unfold symplecticBracket; ring,
    chargePhase_zero, one_smul, label_add_self]

private theorem weyl_mul_neg (v : WeylLabel) : weylMatrix v * weylMatrix (-v) = 1 := by
  rw [weylMatrix_mul, show symplecticBracket v (-v) = 0 by unfold symplecticBracket; simp; ring,
    chargePhase_zero, one_smul, add_neg_cancel, weylMatrix_zero]

private theorem weyl_neg_mul (v : WeylLabel) : weylMatrix (-v) * weylMatrix v = 1 := by
  simpa using weyl_mul_neg (-v)

private theorem weyl_neg_sq (v : WeylLabel) : weylMatrix (-v) * weylMatrix (-v) = weylMatrix v := by
  simpa using weyl_sq (-v)

private theorem phase_shift (b c d : ZMod 3) (h : d = b + c) :
    chargePhase d = chargePhase b * chargePhase c := by rw [h, chargePhase_add]

theorem weylEigen_mul (v : WeylLabel) (b b' : ZMod 3) :
    weylEigenMatrix v b * weylEigenMatrix v b' = if b = b' then weylEigenMatrix v b else 0 := by
  unfold weylEigenMatrix
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, weyl_sq, weyl_mul_neg, weyl_neg_mul, neg_neg]
  have three : ∀ x : ZMod 3, 3 * x = 0 := fun x => by
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
  split_ifs with h
  · subst h
    have hab : chargePhase (-b) * chargePhase b = 1 := by
      rw [mul_comm]; exact chargePhase_mul_neg b
    have hb2 : chargePhase b * chargePhase b = chargePhase (-b) := by
      rw [← chargePhase_add]; congr 1; linear_combination three b
    have ha2 : chargePhase (-b) * chargePhase (-b) = chargePhase b := by
      rw [← chargePhase_add]; congr 1; linear_combination -three b
    linear_combination (norm := module) ((2 / 9 : ℂ) * hab) • (1 : ZMat) +
      ((1 / 9 : ℂ) * hb2) • weylMatrix v + ((1 / 9 : ℂ) * ha2) • weylMatrix (-v)
  · have hc : b - b' ≠ 0 := sub_ne_zero.mpr h
    have hs := character_sum (b - b')
    rw [ite_eq_right hc] at hs
    have h1 : 1 + chargePhase (-b) * chargePhase b' + chargePhase b * chargePhase (-b') = 0 := by
      rw [← chargePhase_add, ← chargePhase_add, show -b + b' = -(b - b') by ring,
        show b + -b' = b - b' by ring]
      linear_combination hs
    have h2 : chargePhase (-b') + chargePhase (-b) + chargePhase b * chargePhase b' = 0 := by
      rw [← chargePhase_add, phase_shift (-b) (b - b') (-b') (by ring),
        phase_shift (-b) (-(b - b')) (b + b') (by linear_combination three b)]
      linear_combination chargePhase (-b) * hs
    have h3 : chargePhase b' + chargePhase (-b) * chargePhase (-b') + chargePhase b = 0 := by
      rw [← chargePhase_add, phase_shift b (-(b - b')) b' (by ring),
        phase_shift b (b - b') (-b + -b') (by linear_combination -three b)]
      linear_combination chargePhase b * hs
    linear_combination (norm := module) ((1 / 9 : ℂ) * h1) • (1 : ZMat) +
      ((1 / 9 : ℂ) * h2) • weylMatrix v + ((1 / 9 : ℂ) * h3) • weylMatrix (-v)

theorem weylEigen_sum (v : WeylLabel) :
    weylEigenMatrix v (outcome 0) + weylEigenMatrix v (outcome 1) + weylEigenMatrix v (outcome 2) = 1 := by
  simp only [weylEigenMatrix, phase_out_zero, phase_out_one, phase_out_two, phase_negout_zero,
    phase_negout_one, phase_negout_two]
  linear_combination (norm := module) ((1 / 3 : ℂ) * chargeRoot_quadratic) • weylMatrix v +
    ((1 / 3 : ℂ) * chargeRoot_quadratic) • weylMatrix (-v)

theorem weylEigen_trace (v : WeylLabel) (hv : v ≠ 0) (b : ZMod 3) :
    Matrix.trace (weylEigenMatrix v b) = 1 := by
  unfold weylEigenMatrix
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    weylMatrix_trace, weylMatrix_trace, if_neg hv, if_neg (neg_ne_zero.mpr hv), Matrix.trace_one]
  simp

private theorem line_pm_ne : ∀ k l : Fin 4, k ≠ l → ∀ s t : ZMod 3, (s = 1 ∨ s = -1) →
    (t = 1 ∨ t = -1) → s • weylLinePoint k + t • weylLinePoint l ≠ 0 := by
  decide

private theorem trace_weyl_pair (k l : Fin 4) (hkl : k ≠ l) (s t : ZMod 3) (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) :
    Matrix.trace (weylMatrix (s • weylLinePoint k) * weylMatrix (t • weylLinePoint l)) = 0 := by
  rw [weylMatrix_mul, Matrix.trace_smul, weylMatrix_trace, if_neg (line_pm_ne k l hkl s t hs ht),
    smul_zero]

theorem weylEigen_unbiased (k l : Fin 4) (hkl : k ≠ l) (b b' : ZMod 3) :
    Matrix.trace (weylEigenMatrix (weylLinePoint k) b * weylEigenMatrix (weylLinePoint l) b') =
      1 / 3 := by
  have p1 := trace_weyl_pair k l hkl 1 1 (Or.inl rfl) (Or.inl rfl)
  have p2 := trace_weyl_pair k l hkl 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have p3 := trace_weyl_pair k l hkl (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have p4 := trace_weyl_pair k l hkl (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simp only [one_smul, neg_one_smul] at p1 p2 p3 p4
  have tk := weylMatrix_trace (weylLinePoint k)
  have tl := weylMatrix_trace (weylLinePoint l)
  have tk' := weylMatrix_trace (-weylLinePoint k)
  have tl' := weylMatrix_trace (-weylLinePoint l)
  rw [if_neg (line_ne_zero k)] at tk
  rw [if_neg (line_ne_zero l)] at tl
  rw [if_neg (neg_ne_zero.mpr (line_ne_zero k))] at tk'
  rw [if_neg (neg_ne_zero.mpr (line_ne_zero l))] at tl'
  unfold weylEigenMatrix
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, p1, p2, p3, p4, tk, tl,
    tk', tl', smul_eq_mul]
  norm_num

/-- The eigenframes in the normal form of `FrameProperties.QutritFourFrames` are frames. -/
theorem weylEigenframe_frame (k : Fin 4) : HermFrame (weylEigenframe k) where
  trace_one a := by
    change (Matrix.trace (weylEigenMatrix (weylLinePoint k) (outcome a))).re = 1
    rw [weylEigen_trace _ (line_ne_zero k), Complex.one_re]
  idempotent a := by
    apply Subtype.ext
    change symZ (weylEigenMatrix (weylLinePoint k) (outcome a))
      (weylEigenMatrix (weylLinePoint k) (outcome a)) = weylEigenMatrix (weylLinePoint k) (outcome a)
    unfold symZ
    rw [weylEigen_mul, if_pos rfl, ← two_smul ℂ, smul_smul]
    norm_num
  orthogonal a b hab := by
    apply Subtype.ext
    have hab' : outcome a ≠ outcome b := hab
    change (1 / 2 : ℂ) • (weylEigenMatrix (weylLinePoint k) (outcome a) *
      weylEigenMatrix (weylLinePoint k) (outcome b) + weylEigenMatrix (weylLinePoint k) (outcome b) *
      weylEigenMatrix (weylLinePoint k) (outcome a)) = 0
    rw [weylEigen_mul, weylEigen_mul, if_neg hab', if_neg (Ne.symm hab'), add_zero, smul_zero]
  sum_unit := by
    apply Subtype.ext
    exact weylEigen_sum _

/-- The four eigenframes are pairwise unbiased. -/
theorem weylEigenframe_unbiased (k l : Fin 4) (hkl : k ≠ l) :
    HermUnbiased (weylEigenframe k) (weylEigenframe l) := by
  intro a b
  change (Matrix.trace ((1 / 2 : ℂ) • (weylEigenMatrix (weylLinePoint k) (outcome a) *
    weylEigenMatrix (weylLinePoint l) (outcome b) + weylEigenMatrix (weylLinePoint l) (outcome b) *
    weylEigenMatrix (weylLinePoint k) (outcome a)))).re = 1 / 3
  rw [Matrix.trace_smul, Matrix.trace_add, weylEigen_unbiased k l hkl,
    weylEigen_unbiased l k (Ne.symm hkl)]
  norm_num


private theorem lineCard : ∀ n : NonzeroCharge, Fintype.card (ChargeLinePoint n) = 4 := by
  decide +kernel

private theorem point_inner_cross {p q : SignedPlaneIndex} (hpq : p ≠ q) (a b : Fin 3) :
    Glennie.inner (point p a) (point q b) = 1 / 3 := by
  have hsplit : ∀ (r : SignedPlaneIndex) (c : Fin 3),
      point r c = (nativeCenter (point r c) : Glennie.Albert) + (1 / 3 : ℝ) • 1 := by
    intro r c
    rw [nativeCenter_coe, Glennie.traceless, (isFrame r).trace_one, sub_add_cancel]
  have hmem : ∀ (r : SignedPlaneIndex) (c : Fin 3), nativeCenter (point r c) ∈ plane r := by
    intro r c
    rw [center_point, plane_eq_range]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  have horth := (Submodule.isOrtho_iff_inner_eq.mp (plane_orthogonal hpq)) _ (hmem p a) _ (hmem q b)
  rw [Submodule.coe_inner, Glennie.hilbert_inner_eq_native] at horth
  have htl : ∀ (r : SignedPlaneIndex) (c : Fin 3),
      Glennie.inner (nativeCenter (point r c) : Glennie.Albert) 1 = 0 := by
    intro r c
    rw [Glennie.inner, Glennie.jordan_unit_right, nativeCenter_coe, Glennie.trace_traceless]
  rw [hsplit p a, hsplit q b, Glennie.inner_add_left, Glennie.inner_add_right,
    Glennie.inner_add_right, Glennie.inner_smul_right, Glennie.inner_smul_left,
    Glennie.inner_smul_left, Glennie.inner_smul_right, horth, htl, Glennie.inner_comm 1, htl]
  rw [Glennie.inner, Glennie.jordan_unit_left, Glennie.trace_unit]
  norm_num

/-- Every hypothesis of `Targets.QutritContrastTable` can hold: the line algebra of the
graded model, its isomorphism with `Herm₃(ℂ)`, and the four native frames on the line. -/
theorem qutritTable_hypotheses_satisfiable :
    ∃ (Q : Submodule ℝ Glennie.Albert) (F : Fin 4 → Fin 3 → Glennie.Albert),
      (1 : Glennie.Albert) ∈ Q ∧ (∀ x y, x ∈ Q → y ∈ Q → Glennie.jordan x y ∈ Q) ∧
      (∃ I : FullHermitian3 ≃ₗ[ℝ] Q,
        ∀ X Y, (I (fullHermitianProduct X Y)).val = Glennie.jordan (I X).val (I Y).val) ∧
      (∀ i, Glennie.Frame (F i)) ∧ (∀ i a, F i a ∈ Q) ∧ (∀ i j, i ≠ j → Unbiased (F i) (F j)) := by
  let l : SignedPlaneIndex := (Fintype.equivFinOfCardEq signedPlaneIndex_card).symm 0
  let e : Fin 4 ≃ ChargeLinePoint l.val := (Fintype.equivFinOfCardEq (lineCard l.val)).symm
  obtain ⟨I, -, -, hI⟩ := nativeLineHermitianModel l
  refine ⟨lineAlgebra l, fun i => point (e i).val, lineAlgebra_one l,
    fun x y hx hy => lineAlgebra_product l hx hy, ⟨I, hI⟩, fun i => isFrame _,
    fun i a => point_mem_lineAlgebra (e i).property a, ?_⟩
  intro i j hij a b
  have hpq : (e i).val ≠ (e j).val := fun h => hij (e.injective (Subtype.ext h))
  exact point_inner_cross hpq a b

end Contrast

end

end ThirteenPlanes.AlbertGrading
