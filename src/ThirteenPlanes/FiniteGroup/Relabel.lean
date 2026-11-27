module

public import ThirteenPlanes.SignedStabilizer.Coefficients
public import ThirteenPlanes.ChargeAction

@[expose] public section

set_option backward.privateInPublic true

/-! Monomial isometries of the signed carrier: a permutation of the nonzero grades compatible with
opposites, with an odd cube-root phase on each grade.  Such a map preserves the equal-strength
cubic exactly when the coupling table is invariant. -/

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

namespace FiniteGroup

open SignedStabilizer

/-- A permutation of the nonzero grades commuting with opposites, with odd phases. -/
structure Relabeling where
  perm : NonzeroCharge ≃ NonzeroCharge
  perm_opposite : ∀ x, perm (oppositeCharge x) = oppositeCharge (perm x)
  phase : NonzeroCharge → ZMod 3
  phase_opposite : ∀ x, phase (oppositeCharge x) = -phase x

namespace Relabeling

variable (R : Relabeling)

theorem perm_symm_opposite (y : NonzeroCharge) :
    R.perm.symm (oppositeCharge y) = oppositeCharge (R.perm.symm y) := by
  apply R.perm.injective
  rw [Equiv.apply_symm_apply, R.perm_opposite, Equiv.apply_symm_apply]

/-- The complex coordinate map: the coordinate at `perm x` is the phase of `x` times that at `x`. -/
def coordMap : (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) where
  toFun Z y := chargePhase (R.phase (R.perm.symm y)) * Z (R.perm.symm y)
  map_add' Z W := by funext y; simp [mul_add]
  map_smul' c Z := by funext y; simp; ring

@[simp] theorem coordMap_apply (Z : NonzeroCharge → ℂ) (y : NonzeroCharge) :
    R.coordMap Z y = chargePhase (R.phase (R.perm.symm y)) * Z (R.perm.symm y) := rfl

theorem coordMap_single (x : NonzeroCharge) :
    R.coordMap (Pi.single x 1) = chargePhase (R.phase x) • Pi.single (R.perm x) 1 := by
  funext y
  simp only [coordMap_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hy : y = R.perm x
  · subst hy; simp
  · have : R.perm.symm y ≠ x := fun h => hy (by rw [← h, Equiv.apply_symm_apply])
    simp [hy, this]

private theorem coordMap_mem (X : SignedField) : R.coordMap (signedCoordinates X) ∈ signedFields := by
  intro y
  simp only [coordMap_apply, perm_symm_opposite, R.phase_opposite, chargePhase_neg,
    signedCoordinates_opposite, star_mul']

/-- The real linear map of the carrier. -/
def toLinearMap : SignedField →ₗ[ℝ] SignedField where
  toFun X := ⟨R.coordMap (signedCoordinates X), R.coordMap_mem X⟩
  map_add' X Y := by
    apply Subtype.ext
    change R.coordMap (signedCoordinates (X + Y)) = R.coordMap (signedCoordinates X) +
      R.coordMap (signedCoordinates Y)
    rw [map_add, map_add]
  map_smul' r X := by
    apply Subtype.ext
    funext y
    change R.coordMap (signedCoordinates (r • X)) y = r • R.coordMap (signedCoordinates X) y
    rw [map_smul]
    change chargePhase _ * (r • signedCoordinates X _) = r • (chargePhase _ * signedCoordinates X _)
    simp only [Complex.real_smul]
    ring

theorem coord_toLinearMap (X : SignedField) :
    signedCoordinates (R.toLinearMap X) = R.coordMap (signedCoordinates X) := rfl

theorem norm_toLinearMap (X : SignedField) : ‖R.toLinearMap X‖ = ‖X‖ := by
  have h : ‖R.toLinearMap X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [signedField_norm_sq, signedField_norm_sq, coord_toLinearMap]
    congr 1
    simp only [coordMap_apply, norm_mul, chargePhase_norm, one_mul]
    exact R.perm.symm.sum_comp (fun x => ‖signedCoordinates X x‖ ^ 2)
  nlinarith [norm_nonneg (R.toLinearMap X), norm_nonneg X]

/-- The relabeling as a linear isometry of the carrier. -/
def toIsometry : SignedField ≃ₗᵢ[ℝ] SignedField :=
  LinearIsometry.toLinearIsometryEquiv ⟨R.toLinearMap, R.norm_toLinearMap⟩ rfl

@[simp] theorem toIsometry_apply (X : SignedField) : R.toIsometry X = R.toLinearMap X := rfl

/-- The coupling table is invariant under the relabeling. -/
def TableInvariant : Prop :=
  ∀ x y w : NonzeroCharge,
    chargePhase (R.phase x + R.phase y + R.phase w) *
      signedCoefficient (R.perm x) (R.perm y) (R.perm w) = signedCoefficient x y w

/-- The relabeling preserves the equal-strength cubic. -/
def PreservesCubic : Prop :=
  ∀ X Y W : SignedField, signedEqualCubic.apply (R.toIsometry X) (R.toIsometry Y) (R.toIsometry W) =
    signedEqualCubic.apply X Y W

private theorem ctCoeff_one : ctCoeff 1 = signedCoefficient := by
  funext i j k; simp [ctCoeff]

private def defect :
    (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ :=
  ((triForm (ctCoeff 1)).compl₁₂ R.coordMap R.coordMap).compr₂ (LinearMap.lcomp ℂ ℂ R.coordMap) -
    triForm (ctCoeff 1)

private theorem defect_apply (Z W U : NonzeroCharge → ℂ) :
    R.defect Z W U = triForm (ctCoeff 1) (R.coordMap Z) (R.coordMap W) (R.coordMap U) -
      triForm (ctCoeff 1) Z W U := rfl

theorem triForm_singles (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (i j k : NonzeroCharge) :
    triForm c (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) = c i j k := by
  rw [triForm_apply]
  simp [Pi.single_apply]

private theorem defect_singles (x y w : NonzeroCharge) :
    R.defect (Pi.single x 1) (Pi.single y 1) (Pi.single w 1) =
      chargePhase (R.phase x + R.phase y + R.phase w) *
        signedCoefficient (R.perm x) (R.perm y) (R.perm w) - signedCoefficient x y w := by
  rw [defect_apply, coordMap_single, coordMap_single, coordMap_single]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, triForm_singles, ctCoeff_one,
    chargePhase_add]
  ring

private theorem triForm_coords (X Y W : SignedField) :
    triForm (ctCoeff 1) (signedCoordinates X) (signedCoordinates Y) (signedCoordinates W) =
      (signedEqualCubic.apply X Y W : ℂ) := by
  rw [triForm_apply, ← signedPair_at_one]
  exact ctSum_eq_apply 1 X Y W

/-- A complex-trilinear table whose form is unchanged by the relabeling on real fields satisfies the
table equation. -/
theorem table_eq_of_invariant (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (hinv : ∀ X Y W : SignedField,
      triForm c (R.coordMap (signedCoordinates X)) (R.coordMap (signedCoordinates Y))
        (R.coordMap (signedCoordinates W)) =
      triForm c (signedCoordinates X) (signedCoordinates Y) (signedCoordinates W))
    (x y w : NonzeroCharge) :
    chargePhase (R.phase x + R.phase y + R.phase w) * c (R.perm x) (R.perm y) (R.perm w) =
      c x y w := by
  let T := ((triForm c).compl₁₂ R.coordMap R.coordMap).compr₂ (LinearMap.lcomp ℂ ℂ R.coordMap) -
    triForm c
  have hT : T = 0 := by
    apply trilinear_ext_of_real
    intro a b d
    change triForm c (R.coordMap _) (R.coordMap _) (R.coordMap _) - triForm c _ _ _ = 0
    rw [hinv, sub_self]
  have h := congrArg (fun T => T (Pi.single x 1) (Pi.single y 1) (Pi.single w 1)) hT
  simp only [LinearMap.zero_apply] at h
  change triForm c (R.coordMap _) (R.coordMap _) (R.coordMap _) - triForm c _ _ _ = 0 at h
  rw [coordMap_single, coordMap_single, coordMap_single] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, triForm_singles] at h
  rw [chargePhase_add, chargePhase_add]
  linear_combination h

/-- A relabeling preserves the cubic exactly when it preserves the coupling table. -/
theorem preservesCubic_iff : R.PreservesCubic ↔ R.TableInvariant := by
  constructor
  · intro h x y w
    have hT : R.defect = 0 := by
      apply trilinear_ext_of_real
      intro a b c
      rw [defect_apply, ← coord_toLinearMap, ← coord_toLinearMap, ← coord_toLinearMap,
        triForm_coords, triForm_coords]
      have := h a b c
      simp only [toIsometry_apply] at this
      rw [this, sub_self]
    have := congrArg (fun T => T (Pi.single x 1) (Pi.single y 1) (Pi.single w 1)) hT
    simp only [defect_singles, LinearMap.zero_apply] at this
    exact sub_eq_zero.mp this
  · intro h X Y W
    have hT : R.defect = 0 := by
      apply (Pi.basisFun ℂ NonzeroCharge).ext; intro x
      apply (Pi.basisFun ℂ NonzeroCharge).ext; intro y
      apply (Pi.basisFun ℂ NonzeroCharge).ext; intro w
      simp only [Pi.basisFun_apply, defect_singles, LinearMap.zero_apply, h x y w, sub_self]
    have := congrArg (fun T => T (signedCoordinates X) (signedCoordinates Y) (signedCoordinates W)) hT
    simp only [defect_apply, LinearMap.zero_apply, ← coord_toLinearMap, triForm_coords] at this
    simp only [toIsometry_apply]
    exact_mod_cast sub_eq_zero.mp this

/-- Relabelings preserve the diagonal cubic. -/
theorem preserves_diagonal (X Y W : SignedField) :
    signedDiagonalCubic.apply (R.toIsometry X) (R.toIsometry Y) (R.toIsometry W) =
      signedDiagonalCubic.apply X Y W := by
  rw [signedDiagonalCubic_sum, signedDiagonalCubic_sum]
  congr 1
  simp only [toIsometry_apply, coord_toLinearMap, coordMap_apply]
  rw [← R.perm.symm.sum_comp (fun i => (signedCoordinates X i * signedCoordinates Y i *
    signedCoordinates W i).re)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h3 : chargePhase (R.phase (R.perm.symm i)) ^ 3 = 1 := by
    rw [chargePhase, ← pow_mul, mul_comm, pow_mul, chargeRoot_cube, one_pow]
  linear_combination (signedCoordinates X (R.perm.symm i) * signedCoordinates Y (R.perm.symm i) *
    signedCoordinates W (R.perm.symm i)) * h3

end Relabeling

end FiniteGroup

end

end ThirteenPlanes
