module

public import ThirteenPlanes.ChargeAction
public import ThirteenPlanes.SignedSupport

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

/-- A relabeling and odd phase that preserve the signed grade multiplication. -/
structure GradeLift where
  relabel : Charge ≃+ Charge
  phase : Charge → ZMod 3
  odd : ∀ x, phase (-x) = -phase x
  cocycle : ∀ x y, gradeExponent (relabel x) (relabel y) +
    (phase x + phase y - phase (x+y)) = gradeExponent x y

namespace GradeLift

def identity : GradeLift where
  relabel := AddEquiv.refl _
  phase _ := 0
  odd _ := by simp
  cocycle _ _ := by simp

def trans (g h : GradeLift) : GradeLift where
  relabel := g.relabel.trans h.relabel
  phase x := g.phase x + h.phase (g.relabel x)
  odd x := by rw [g.odd, map_neg, h.odd, neg_add]
  cocycle x y := by
    change gradeExponent (h.relabel (g.relabel x)) (h.relabel (g.relabel y)) +
      ((g.phase x + h.phase (g.relabel x)) + (g.phase y + h.phase (g.relabel y)) -
        (g.phase (x+y) + h.phase (g.relabel (x+y)))) = _
    rw [map_add]
    linear_combination g.cocycle x y + h.cocycle (g.relabel x) (g.relabel y)

/-- Forgetting the zero coordinate restricts the grade relabeling to a permutation. -/
def nonzeroEquiv (g : GradeLift) : NonzeroCharge ≃ NonzeroCharge where
  toFun x := ⟨g.relabel x.val, fun h => x.property (g.relabel.injective (h.trans (map_zero _).symm))⟩
  invFun x := ⟨g.relabel.symm x.val, fun h => x.property
    (g.relabel.symm.injective (h.trans (map_zero _).symm))⟩
  left_inv x := Subtype.ext (g.relabel.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.relabel.apply_symm_apply x.val)

@[simp] theorem nonzeroEquiv_val (g : GradeLift) (x : NonzeroCharge) :
    (g.nonzeroEquiv x).val = g.relabel x.val := rfl

private theorem nonzeroEquiv_symm_opposite (g : GradeLift) (x : NonzeroCharge) :
    g.nonzeroEquiv.symm (oppositeCharge x) = oppositeCharge (g.nonzeroEquiv.symm x) :=
  Subtype.ext (map_neg g.relabel.symm x.val)

private def values (g : GradeLift) (x : SignedField) (q : NonzeroCharge) : ℂ :=
  chargePhase (g.phase (g.nonzeroEquiv.symm q).val) * signedCoordinates x (g.nonzeroEquiv.symm q)

private theorem values_mem (g : GradeLift) (x : SignedField) :
    g.values x ∈ signedFields := by
  intro q
  simp only [values, nonzeroEquiv_symm_opposite, signedCoordinates_opposite]
  change chargePhase (g.phase (-(g.nonzeroEquiv.symm q).val)) *
    star (signedCoordinates x (g.nonzeroEquiv.symm q)) = _
  rw [g.odd, chargePhase_neg, star_mul, mul_comm]

private def fieldLinear (g : GradeLift) : SignedField →ₗ[ℝ] SignedField where
  toFun x := ⟨g.values x, g.values_mem x⟩
  map_add' x y := by
    apply signedFields.subtype_injective
    funext q
    change g.values (x + y) q = g.values x q + g.values y q
    simp [values, mul_add]
  map_smul' r x := by
    apply signedFields.subtype_injective
    funext q
    change g.values (r • x) q = r • g.values x q
    simp only [values, map_smul, Pi.smul_apply, mul_smul_comm]

private theorem fieldLinear_norm (g : GradeLift) (x : SignedField) :
    ‖g.fieldLinear x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [signedField_norm_sq]
  change 3 * ∑ q, ‖g.values x q‖ ^ 2 = 3 * ∑ q, ‖signedCoordinates x q‖ ^ 2
  simp only [values, norm_mul, chargePhase_norm, one_mul]
  congr 1
  exact Equiv.sum_comp g.nonzeroEquiv.symm (fun q => ‖signedCoordinates x q‖ ^ 2)

/-- The lifted grade relabeling acts by a real orthogonal equivalence. -/
def action (g : GradeLift) : SignedField ≃ₗᵢ[ℝ] SignedField := by
  let f : SignedField →ₗᵢ[ℝ] SignedField := ⟨g.fieldLinear, g.fieldLinear_norm⟩
  let e := LinearEquiv.ofBijective g.fieldLinear
    ⟨f.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp f.injective⟩
  exact ⟨e, g.fieldLinear_norm⟩

@[simp] theorem action_coordinates (g : GradeLift) (x : SignedField) (q : NonzeroCharge) :
    signedCoordinates (g.action x) (g.nonzeroEquiv q) =
      chargePhase (g.phase q.val) * signedCoordinates x q := by
  change g.values x (g.nonzeroEquiv q) = _
  simp [values]

private theorem exponent_dependent_zero {x y : Charge} (h : dependentGrades x y) :
    gradeExponent x y = 0 := by
  rcases h with h | h | h | h
  · subst x
    simp [gradeExponent]
  · subst y
    simp [gradeExponent]
  · subst y
    simp [gradeExponent]
  · subst x
    simp only [gradeExponent, Pi.neg_apply]
    ring

private theorem dependentRelabel (g : GradeLift) (x y : Charge) :
    dependentGrades (g.relabel x) (g.relabel y) ↔ dependentGrades x y := by
  have hz (w : Charge) : g.relabel w = 0 ↔ w = 0 := by
    rw [← map_zero g.relabel, g.relabel.injective.eq_iff, map_zero]
  have ho : g.relabel x = -g.relabel y ↔ x = -y := by
    rw [← map_neg, g.relabel.injective.eq_iff]
  exact or_congr (hz x) (or_congr (hz y) (or_congr g.relabel.injective.eq_iff ho))

private theorem gradeSumRelabel (g : GradeLift) (x y z : Charge) :
    g.relabel x + g.relabel y + g.relabel z = 0 ↔ x+y+z = 0 := by
  rw [← map_add, ← map_add, ← map_zero g.relabel, g.relabel.injective.eq_iff, map_zero]

private theorem coefficient_action (g : GradeLift) (i j k : NonzeroCharge) :
    signedCoefficient (g.nonzeroEquiv i) (g.nonzeroEquiv j) (g.nonzeroEquiv k) *
      chargePhase (g.phase i.val) * chargePhase (g.phase j.val) * chargePhase (g.phase k.val) =
      signedCoefficient i j k := by
  change (gradedProductCoefficient (g.relabel i.val) (g.relabel j.val) *
      gradeMetric (g.relabel i.val + g.relabel j.val) (g.relabel k.val)) *
      chargePhase (g.phase i.val) * chargePhase (g.phase j.val) * chargePhase (g.phase k.val) = _
  have hg := g.gradeSumRelabel i.val j.val k.val
  by_cases hs : i.val + j.val + k.val = 0
  · have hz : k.val = -(i.val+j.val) := eq_neg_of_add_eq_zero_right hs
    have he : gradeExponent (g.relabel i.val) (g.relabel j.val) +
        (g.phase i.val + g.phase j.val + g.phase k.val) = gradeExponent i.val j.val := by
      rw [hz, g.odd]
      simpa only [sub_eq_add_neg] using g.cocycle i.val j.val
    have hc : gradedProductCoefficient (g.relabel i.val) (g.relabel j.val) *
        chargePhase (g.phase i.val + g.phase j.val + g.phase k.val) =
        gradedProductCoefficient i.val j.val := by
      by_cases hp : dependentGrades i.val j.val
      · have hh := (g.dependentRelabel _ _).mpr hp
        rw [exponent_dependent_zero hh, exponent_dependent_zero hp, zero_add] at he
        simp [gradedProductCoefficient, hp, hh, he]
      · have hh := not_iff_not.mpr (g.dependentRelabel i.val j.val) |>.mpr hp
        simp only [gradedProductCoefficient, hp, hh, ↓reduceIte]
        change -(chargePhase (gradeExponent (g.relabel i.val) (g.relabel j.val))) / 2 *
            chargePhase (g.phase i.val + g.phase j.val + g.phase k.val) =
          -(chargePhase (gradeExponent i.val j.val)) / 2
        rw [← he, chargePhase_add (gradeExponent (g.relabel i.val) (g.relabel j.val))
          (g.phase i.val + g.phase j.val + g.phase k.val)]
        ring
    simp only [gradeMetric, hg.mpr hs, ↓reduceIte, signedCoefficient, hs]
    calc
      _ = (gradedProductCoefficient (g.relabel i.val) (g.relabel j.val) *
          chargePhase (g.phase i.val + g.phase j.val + g.phase k.val)) * 3 := by
        simp only [chargePhase_add]
        ring
      _ = _ := by rw [hc]
  · have hh := not_iff_not.mpr hg |>.mpr hs
    simp [gradeMetric, signedCoefficient, hs, hh]

private theorem diagonal_action (g : GradeLift) (i j k : NonzeroCharge) :
    signedDiagonalCoefficient (g.nonzeroEquiv i) (g.nonzeroEquiv j) (g.nonzeroEquiv k) *
      chargePhase (g.phase i.val) * chargePhase (g.phase j.val) * chargePhase (g.phase k.val) =
      signedDiagonalCoefficient i j k := by
  simp only [signedDiagonalCoefficient, g.nonzeroEquiv.injective.eq_iff]
  by_cases h : i = j ∧ j = k
  · rcases h with ⟨rfl, rfl⟩
    simp only [true_and, ↓reduceIte]
    have hsum : g.phase i.val + g.phase i.val + g.phase i.val = 0 := by
      linear_combination g.phase i.val * (by decide : (3 : ZMod 3) = 0)
    have hph := congrArg chargePhase hsum
    simp only [chargePhase_add, chargePhase_zero] at hph
    linear_combination 3 * hph
  · simp [h]

private theorem apply_charge_table_invariant (g : GradeLift)
    (h : SymmetricCubic SignedField) (coeff : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (happly : ∀ x y z : SignedField, h.apply x y z =
      ∑ i, ∑ j, ∑ k,
        (coeff i j k * signedCoordinates x i * signedCoordinates y j * signedCoordinates z k).re)
    (hcoeff : ∀ i j k, coeff (g.nonzeroEquiv i) (g.nonzeroEquiv j) (g.nonzeroEquiv k) *
      chargePhase (g.phase i.val) * chargePhase (g.phase j.val) * chargePhase (g.phase k.val) =
        coeff i j k)
    (x y z : SignedField) : h.apply (g.action x) (g.action y) (g.action z) = h.apply x y z := by
  rw [happly, happly]
  rw [← Equiv.sum_comp g.nonzeroEquiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp g.nonzeroEquiv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Equiv.sum_comp g.nonzeroEquiv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [action_coordinates]
  congr 1
  rw [← hcoeff i j k]
  ring

theorem preserves_full (g : GradeLift) (x y z : SignedField) :
    signedEqualCubic.apply (g.action x) (g.action y) (g.action z) = signedEqualCubic.apply x y z :=
  g.apply_charge_table_invariant _ _ signedEqualCubic_apply g.coefficient_action x y z

theorem preserves_diagonal (g : GradeLift) (x y z : SignedField) :
    signedDiagonalCubic.apply (g.action x) (g.action y) (g.action z) = signedDiagonalCubic.apply x y z :=
  g.apply_charge_table_invariant _ _ signedDiagonalCubic_apply g.diagonal_action x y z

theorem preserves_coupling (g : GradeLift) (v : ℝ × ℝ) (x y z : SignedField) :
    (coupling signedPair v).apply (g.action x) (g.action y) (g.action z) =
      (coupling signedPair v).apply x y z := by
  have hsub (a b c : SignedField) :
      (signedEqualCubic - signedDiagonalCubic).apply a b c =
        signedEqualCubic.apply a b c - signedDiagonalCubic.apply a b c := by
    simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]
  simp only [coupling_apply, signedPair, SymmetricCubic.apply_add, SymmetricCubic.apply_smul,
    hsub, g.preserves_full, g.preserves_diagonal]

theorem preserves_square (g : GradeLift) (v : ℝ × ℝ) (x : SignedField) :
    (coupling signedPair v).squareMap (g.action x) =
      g.action ((coupling signedPair v).squareMap x) := by
  apply ext_inner_right ℝ
  intro y
  obtain ⟨z, rfl⟩ := g.action.surjective y
  rw [g.action.inner_map_map]
  exact g.preserves_coupling v x x z

end GradeLift

end

end ThirteenPlanes
