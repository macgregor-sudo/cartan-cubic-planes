module

public import ThirteenPlanes.FiniteGroup.Tables
public import ThirteenPlanes.FiniteGroup.Transitive
public import ThirteenPlanes.FiniteGroup.CodeLifts

@[expose] public section

set_option backward.privateInPublic true

/-! Real trilinear forms invariant under the finite code group are combinations of the diagonal and
mixing cubics: the charges force zero-sum support, and the special linear group is transitive on the
two orbits of zero-sum triples of nonzero grades. -/

open Matrix
open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

namespace FiniteGroup

open SignedStabilizer

local notation "z" => signedCoordinates

/-- Invariance of a real trilinear form under every lift of a determinant-one relabeling that
preserves the equal-strength cubic. -/
def IsCodeInvariant (f : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ) : Prop :=
  ∀ (A : SpecialLinearGroup (Fin 3) (ZMod 3)) (F : Charge → ZMod 3) (hF : IsOddPhase F),
    (codeRelabeling A F hF).PreservesCubic → ∀ X Y W : SignedField,
      f ((codeRelabeling A F hF).toIsometry X) ((codeRelabeling A F hF).toIsometry Y)
        ((codeRelabeling A F hF).toIsometry W) = f X Y W

variable {f : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ}

private theorem table_eq (hf : IsCodeInvariant f) (A : SpecialLinearGroup (Fin 3) (ZMod 3))
    (F : Charge → ZMod 3) (hF : IsOddPhase F) (hp : (codeRelabeling A F hF).PreservesCubic)
    (x y w : NonzeroCharge) :
    chargePhase (F x.val + F y.val + F w.val) *
      tableOf f (chargeAct A x) (chargeAct A y) (chargeAct A w) = tableOf f x y w :=
  (codeRelabeling A F hF).table_eq_of_invariant (tableOf f) (fun X Y W => by
    rw [← Relabeling.coord_toLinearMap, ← Relabeling.coord_toLinearMap,
      ← Relabeling.coord_toLinearMap, ← trilinear_eq_triForm, ← trilinear_eq_triForm]
    have := hf A F hF hp X Y W
    simp only [Relabeling.toIsometry_apply] at this
    rw [this]) x y w

private theorem coef_eq (A : SpecialLinearGroup (Fin 3) (ZMod 3))
    (F : Charge → ZMod 3) (hF : IsOddPhase F) (hp : (codeRelabeling A F hF).PreservesCubic)
    (x y w : NonzeroCharge) :
    chargePhase (F x.val + F y.val + F w.val) *
      signedCoefficient (chargeAct A x) (chargeAct A y) (chargeAct A w) = signedCoefficient x y w :=
  ((codeRelabeling A F hF).preservesCubic_iff.mp hp) x y w

private theorem chargeAct_one (x : NonzeroCharge) : chargeAct 1 x = x :=
  Subtype.ext (by simp [chargeAct_val])

private theorem chargePhase_ne_one {a : ZMod 3} (ha : a ≠ 0) : chargePhase a ≠ 1 := by
  intro h
  exact ha (chargePhase_injective (h.trans chargePhase_zero.symm))

/-- Charge invariance: the table vanishes off zero-sum triples. -/
private theorem table_support (hf : IsCodeInvariant f) {x y w : NonzeroCharge}
    (hs : x.val + y.val + w.val ≠ 0) : tableOf f x y w = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, (x.val + y.val + w.val) k ≠ 0 := by
    by_contra h
    apply hs
    funext m
    by_contra hm
    exact h ⟨m, hm⟩
  let F : Charge → ZMod 3 := fun v => v k
  have hF : IsOddPhase F := fun v => rfl
  have hp : (codeRelabeling 1 F hF).PreservesCubic := by
    rw [codeRelabeling_preserves_iff]
    intro a b _
    simp [F]
  have e := table_eq hf 1 F hF hp x y w
  simp only [chargeAct_one] at e
  have hph : chargePhase (F x.val + F y.val + F w.val) ≠ 1 := chargePhase_ne_one hk
  have : (chargePhase (F x.val + F y.val + F w.val) - 1) * tableOf f x y w = 0 := by
    linear_combination e
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hph)

private theorem diag_zero {i j k : NonzeroCharge} (hs : i.val + j.val + k.val ≠ 0) :
    signedDiagonalCoefficient i j k = 0 := by
  unfold signedDiagonalCoefficient
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    exact absurd (show i.val + i.val + i.val = 0 by
      funext m; change i.val m + i.val m + i.val m = 0
      linear_combination i.val m * (by decide : (3 : ZMod 3) = 0)) hs
  · rfl

private def e0 : NonzeroCharge := ⟨Pi.single 0 1, by decide⟩
private def e1 : NonzeroCharge := ⟨Pi.single 1 1, by decide⟩
private def e2 : NonzeroCharge := ⟨-(Pi.single 0 1 + Pi.single 1 1), by decide⟩

private theorem e01_independent : ¬ dependentGrades e0.val e1.val := by
  unfold dependentGrades e0 e1; decide

private theorem e012_sum : e0.val + e1.val + e2.val = 0 := by
  unfold e0 e1 e2; decide

/-- The table of a code-invariant trilinear form is a combination of the diagonal and coupling
tables. -/
private theorem table_formula (hf : IsCodeInvariant f) (i j k : NonzeroCharge) :
    tableOf f i j k =
      (tableOf f e0 e0 e0 / 3 - tableOf f e0 e1 e2 / signedCoefficient e0 e1 e2) *
          signedDiagonalCoefficient i j k +
        tableOf f e0 e1 e2 / signedCoefficient e0 e1 e2 * signedCoefficient i j k := by
  have hS0 : signedCoefficient e0 e1 e2 ≠ 0 :=
    signedCoefficient_ne_zero_of_grade_sum_zero _ _ _ e012_sum
  by_cases hs : i.val + j.val + k.val = 0
  · by_cases hd : dependentGrades i.val j.val
    · -- the diagonal orbit
      have h3c : (3 : Charge) = 0 := by decide
      have hij : i = j ∧ k = i := by
        rcases hd with e | e | e | e
        · exact absurd e i.property
        · exact absurd e j.property
        · refine ⟨Subtype.ext e, Subtype.ext ?_⟩
          rw [← e] at hs
          linear_combination hs - i.val * h3c
        · exfalso; apply k.property; rw [e] at hs; linear_combination hs
      rw [← hij.1, hij.2]
      obtain ⟨A, hA⟩ := sl_transitive e0.property i.property
      obtain ⟨F, hF, hp⟩ := codeLift_exists A
      have e := table_eq hf A F hF hp e0 e0 e0
      have hAi : chargeAct A e0 = i := Subtype.ext hA
      rw [hAi, show F e0.val + F e0.val + F e0.val = 0 by
        linear_combination F e0.val * (by decide : (3 : ZMod 3) = 0), chargePhase_zero,
        one_mul] at e
      rw [e, signedCoefficient_diagonal]
      simp only [signedDiagonalCoefficient, and_self, ↓reduceIte]
      field_simp
      ring
    · -- the independent orbit
      obtain ⟨A, hA0, hA1⟩ := sl_transitive_pairs e01_independent hd
      obtain ⟨F, hF, hp⟩ := codeLift_exists A
      have hA2 : chargeAct A e2 = k := by
        apply Subtype.ext
        change (A : ChargeMatrix) *ᵥ (-(Pi.single 0 1 + Pi.single 1 1)) = k.val
        rw [Matrix.mulVec_neg, Matrix.mulVec_add]
        change -((A : ChargeMatrix) *ᵥ e0.val + (A : ChargeMatrix) *ᵥ e1.val) = k.val
        rw [hA0, hA1]
        linear_combination -hs
      have hAi : chargeAct A e0 = i := Subtype.ext hA0
      have hAj : chargeAct A e1 = j := Subtype.ext hA1
      have eT := table_eq hf A F hF hp e0 e1 e2
      have eS := coef_eq A F hF hp e0 e1 e2
      rw [hAi, hAj, hA2] at eT eS
      have hij : i ≠ j := fun h => hd (Or.inr (Or.inr (Or.inl (congrArg Subtype.val h))))
      have hdiag : signedDiagonalCoefficient i j k = 0 := by
        simp [signedDiagonalCoefficient, hij]
      rw [hdiag, mul_zero, zero_add, ← eT, ← eS]
      have hSij : signedCoefficient i j k ≠ 0 :=
        signedCoefficient_ne_zero_of_grade_sum_zero _ _ _ hs
      have hp0 : chargePhase (F e0.val + F e1.val + F e2.val) ≠ 0 := by
        intro h0
        have := chargePhase_norm (F e0.val + F e1.val + F e2.val)
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      field_simp
  · rw [table_support hf hs, diag_zero hs, signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ hs]
    ring

private theorem triForm_combination (a b : ℂ)
    (c d : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ) (Z W U : NonzeroCharge → ℂ) :
    triForm (fun i j k => a * c i j k + b * d i j k) Z W U =
      a * triForm c Z W U + b * triForm d Z W U := by
  simp only [triForm_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem triForm_diagonal (X Y W : SignedField) :
    triForm signedDiagonalCoefficient (z X) (z Y) (z W) =
      (signedPair.diagonalCubic.apply X Y W : ℂ) := by
  have hc : ctCoeff 0 = signedDiagonalCoefficient := by funext i j k; simp [ctCoeff]
  rw [← hc, triForm_apply]
  change ctSum 0 X Y W = _
  rw [ctSum_eq_apply]
  congr 1
  simp [interactionCubic, signedPair]

private theorem triForm_equal (X Y W : SignedField) :
    triForm signedCoefficient (z X) (z Y) (z W) = (signedEqualCubic.apply X Y W : ℂ) := by
  have hc : ctCoeff 1 = signedCoefficient := by funext i j k; simp [ctCoeff]
  rw [← hc, triForm_apply]
  change ctSum 1 X Y W = _
  rw [ctSum_eq_apply, signedPair_at_one]

private theorem mixing_apply (X Y W : SignedField) :
    signedPair.mixingCubic.apply X Y W =
      signedEqualCubic.apply X Y W - signedPair.diagonalCubic.apply X Y W := by
  have := SymmetricCubic.apply_add signedPair.mixingCubic signedPair.diagonalCubic X Y W
  have e : signedPair.mixingCubic + signedPair.diagonalCubic = signedEqualCubic := by
    simp only [signedPair]
    exact sub_add_cancel signedEqualCubic signedDiagonalCubic
  rw [e] at this
  linarith

/-- A real trilinear form on the signed carrier invariant under the code group is a real combination
of the diagonal and mixing cubics. -/
theorem codeInvariant_trilinear (hf : IsCodeInvariant f) :
    ∃ a b : ℝ, ∀ X Y W : SignedField,
      f X Y W = a * signedPair.diagonalCubic.apply X Y W + b * signedPair.mixingCubic.apply X Y W := by
  set α := tableOf f e0 e0 e0 / 3
  set β := tableOf f e0 e1 e2 / signedCoefficient e0 e1 e2
  refine ⟨α.re, β.re, fun X Y W => ?_⟩
  have h := trilinear_eq_triForm f X Y W
  have ht : tableOf f = fun i j k => (α - β) * signedDiagonalCoefficient i j k +
      β * signedCoefficient i j k := by
    funext i j k; exact table_formula hf i j k
  rw [ht, triForm_combination, triForm_diagonal, triForm_equal] at h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.add_re, Complex.re_mul_ofReal, Complex.sub_re] at hre
  rw [hre, mixing_apply]
  ring

/-- The diagonal cubic is code invariant. -/
theorem diagonal_isCodeInvariant : IsCodeInvariant signedPair.diagonalCubic.trilinear := by
  intro A F hF _ X Y W
  exact (codeRelabeling A F hF).preserves_diagonal X Y W

/-- The mixing cubic is code invariant. -/
theorem mixing_isCodeInvariant : IsCodeInvariant signedPair.mixingCubic.trilinear := by
  intro A F hF hp X Y W
  simp only [SymmetricCubic.trilinear_apply, mixing_apply]
  rw [hp X Y W]
  have := (codeRelabeling A F hF).preserves_diagonal X Y W
  simp only [signedPair] at this ⊢
  rw [this]

/-- The diagonal and mixing cubics are linearly independent. -/
theorem diagonal_mixing_independent {a b : ℝ}
    (h : ∀ X Y W : SignedField,
      a * signedPair.diagonalCubic.apply X Y W + b * signedPair.mixingCubic.apply X Y W = 0) :
    a = 0 ∧ b = 0 := by
  let c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ :=
    fun i j k => ((a - b : ℝ) : ℂ) * signedDiagonalCoefficient i j k + (b : ℂ) * signedCoefficient i j k
  have hT : triForm c = 0 := by
    apply trilinear_ext_of_real
    intro X Y W
    rw [triForm_combination, triForm_diagonal, triForm_equal]
    have := h X Y W
    rw [mixing_apply] at this
    have hc : ((a * signedPair.diagonalCubic.apply X Y W +
      b * (signedEqualCubic.apply X Y W - signedPair.diagonalCubic.apply X Y W) : ℝ) : ℂ) = 0 := by
      rw [this]; simp
    push_cast at hc ⊢
    linear_combination hc
  have hc : ∀ i j k, c i j k = 0 := by
    intro i j k
    have := congrArg (fun T => T (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)) hT
    simpa only [Relabeling.triForm_singles, LinearMap.zero_apply] using this
  have h01 : e0 ≠ e1 := by
    intro h; have := congrArg Subtype.val h; revert this; unfold e0 e1; decide
  have hb : (b : ℂ) = 0 := by
    have := hc e0 e1 e2
    simp only [c, signedDiagonalCoefficient, h01, false_and, ↓reduceIte, mul_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_right
      (signedCoefficient_ne_zero_of_grade_sum_zero _ _ _ e012_sum)
  have hb' : b = 0 := by exact_mod_cast hb
  refine ⟨?_, hb'⟩
  have := hc e0 e0 e0
  simp only [c, signedDiagonalCoefficient, and_self, ↓reduceIte,
    hb', Complex.ofReal_zero, zero_mul, add_zero, sub_zero] at this
  have : ((a : ℝ) : ℂ) = 0 := by linear_combination this / 3
  exact_mod_cast this

/-- The code-invariant symmetric cubics are exactly the real combinations of the diagonal and mixing
cubics. -/
theorem codeInvariant_cubic_iff (h : SymmetricCubic SignedField) :
    IsCodeInvariant h.trilinear ↔
      ∃ a b : ℝ, h = a • signedPair.diagonalCubic + b • signedPair.mixingCubic := by
  constructor
  · intro hf
    obtain ⟨a, b, hab⟩ := codeInvariant_trilinear hf
    exact ⟨a, b, SymmetricCubic.ext fun X Y W => by simpa using hab X Y W⟩
  · rintro ⟨a, b, rfl⟩ A F hF hp X Y W
    have h1 := diagonal_isCodeInvariant A F hF hp X Y W
    have h2 := mixing_isCodeInvariant A F hF hp X Y W
    simp only [SymmetricCubic.trilinear_apply] at h1 h2 ⊢
    simp only [SymmetricCubic.apply_add, SymmetricCubic.apply_smul, h1, h2]

end FiniteGroup

end

end ThirteenPlanes
