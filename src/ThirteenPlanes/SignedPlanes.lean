module

public import ThirteenPlanes.SignedMetric
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true

/-! The thirteen real coordinate planes of the signed ternary carrier. -/

namespace ThirteenPlanes

noncomputable section

/-- Select the grade whose first nonzero coordinate is `1`. -/
def isChargeRepresentative (x : Charge) : Prop :=
  x 0 = 1 ∨ (x 0 = 0 ∧ x 1 = 1) ∨ (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1)

instance : DecidablePred isChargeRepresentative := fun x ↦
  inferInstanceAs (Decidable
    (x 0 = 1 ∨ (x 0 = 0 ∧ x 1 = 1) ∨ (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1)))

/-- An index of one of the real two-planes. -/
abbrev SignedPlaneIndex := {x : NonzeroCharge // isChargeRepresentative x.val}

private theorem charge_rep_of_neg_iff :
    ∀ x : Charge, x ≠ 0 → (isChargeRepresentative (-x) ↔ ¬ isChargeRepresentative x) := by
  decide

theorem oppositeCharge_isRepresentative_iff (x : NonzeroCharge) :
    isChargeRepresentative (oppositeCharge x).val ↔ ¬ isChargeRepresentative x.val :=
  charge_rep_of_neg_iff x.val x.property

/-- Each nonzero grade is represented uniquely by a selected grade and a sign. -/
def signedPlaneGradeEquiv : SignedPlaneIndex × Bool ≃ NonzeroCharge where
  toFun p := if p.2 then oppositeCharge p.1.val else p.1.val
  invFun x := if hx : isChargeRepresentative x.val then (⟨x, hx⟩, false)
    else (⟨oppositeCharge x, (oppositeCharge_isRepresentative_iff x).mpr hx⟩, true)
  left_inv := by
    rintro ⟨p, sign⟩
    cases sign
    · simp only [Bool.false_eq_true, ↓reduceIte, dite_eq_left p.property]
    · have hp := fun h ↦ (oppositeCharge_isRepresentative_iff p.val).mp h p.property
      simp only [↓reduceIte, dite_eq_right hp, oppositeCharge_opposite]
  right_inv := by
    intro x
    by_cases hx : isChargeRepresentative x.val <;> simp [hx]

@[simp] theorem signedPlaneGradeEquiv_false (p : SignedPlaneIndex) :
    signedPlaneGradeEquiv (p, false) = p.val := rfl

@[simp] theorem signedPlaneGradeEquiv_true (p : SignedPlaneIndex) :
    signedPlaneGradeEquiv (p, true) = oppositeCharge p.val := rfl

theorem nonzeroCharge_card : Fintype.card NonzeroCharge = 26 := by
  change Fintype.card {x : Charge // ¬ x = 0} = 26
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp [Charge]

theorem signedPlaneIndex_card : Fintype.card SignedPlaneIndex = 13 := by
  have h := Fintype.card_congr signedPlaneGradeEquiv
  rw [Fintype.card_prod, Fintype.card_bool, nonzeroCharge_card] at h
  omega

@[simp] theorem signedCoordinates_opposite (x : SignedField) (i : NonzeroCharge) :
    signedCoordinates x (oppositeCharge i) = star (signedCoordinates x i) := x.property i

private def restrictSignedCoordinates : SignedField →ₗ[ℝ] (SignedPlaneIndex → ℂ) where
  toFun x p := signedCoordinates x p.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def extendSignedCoordinates (f : SignedPlaneIndex → ℂ) (x : NonzeroCharge) : ℂ :=
  if hx : isChargeRepresentative x.val then f ⟨x, hx⟩
  else star (f ⟨oppositeCharge x, (oppositeCharge_isRepresentative_iff x).mpr hx⟩)

private theorem extendSignedCoordinates_mem (f : SignedPlaneIndex → ℂ) :
    extendSignedCoordinates f ∈ signedFields := by
  intro x
  have hop := oppositeCharge_isRepresentative_iff x
  by_cases hx : isChargeRepresentative x.val
  · have hn := fun h ↦ hop.mp h hx
    simp only [extendSignedCoordinates, dite_eq_left hx, dite_eq_right hn, oppositeCharge_opposite]
  · simp only [extendSignedCoordinates, dite_eq_left (hop.mpr hx), dite_eq_right hx, star_star]

/-- Restriction to the representatives identifies the real form with thirteen complex coordinates. -/
def signedPlaneCoordinates : SignedField ≃ₗ[ℝ] (SignedPlaneIndex → ℂ) := by
  refine LinearEquiv.ofBijective restrictSignedCoordinates ⟨?_, ?_⟩
  · intro x y h
    apply signedFields.subtype_injective
    funext i
    by_cases hi : isChargeRepresentative i.val
    · exact congrFun h ⟨i, hi⟩
    · change signedCoordinates x i = signedCoordinates y i
      have hh := congrFun h ⟨oppositeCharge i, (oppositeCharge_isRepresentative_iff i).mpr hi⟩
      change signedCoordinates x (oppositeCharge i) = signedCoordinates y (oppositeCharge i) at hh
      simpa only [signedCoordinates_opposite, star_star] using congrArg star hh
  · intro f
    refine ⟨⟨extendSignedCoordinates f, extendSignedCoordinates_mem f⟩, ?_⟩
    funext p
    change extendSignedCoordinates f p.val = f p
    rw [extendSignedCoordinates, dite_eq_left p.property]

@[simp] theorem signedPlaneCoordinates_apply (x : SignedField) (p : SignedPlaneIndex) :
    signedPlaneCoordinates x p = signedCoordinates x p.val := rfl

theorem signedField_finrank : Module.finrank ℝ SignedField = 26 := by
  rw [signedPlaneCoordinates.finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, signedPlaneIndex_card]

/-- The kinetic norm gives weight six to each representative complex coordinate. -/
theorem signedField_norm_sq_representatives (x : SignedField) :
    ‖x‖ ^ 2 = 6 * ∑ p, ‖signedPlaneCoordinates x p‖ ^ 2 := by
  rw [signedField_norm_sq,
    ← signedPlaneGradeEquiv.sum_comp (fun q ↦ ‖signedCoordinates x q‖ ^ 2), Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, signedPlaneGradeEquiv_true, signedPlaneGradeEquiv_false,
    signedCoordinates_opposite, Complex.star_def, Complex.norm_conj, ← signedPlaneCoordinates_apply,
    ← two_mul,
    ← Finset.mul_sum]
  ring

/-- A complex coordinate included as a real field on its opposite pair of grades. -/
def signedPlaneInclusion (p : SignedPlaneIndex) : ℂ →ₗ[ℝ] SignedField :=
  signedPlaneCoordinates.symm.toLinearMap.comp (LinearMap.single ℝ (fun _ ↦ ℂ) p)

@[simp] theorem signedPlaneCoordinates_inclusion (p : SignedPlaneIndex) (z : ℂ) :
    signedPlaneCoordinates (signedPlaneInclusion p z) = Pi.single p z := by
  change signedPlaneCoordinates (signedPlaneCoordinates.symm (Pi.single p z)) = _
  exact signedPlaneCoordinates.apply_symm_apply _

theorem signedCoordinates_inclusion_representative (p q : SignedPlaneIndex) (z : ℂ) :
    signedCoordinates (signedPlaneInclusion p z) q.val = (Pi.single p z : SignedPlaneIndex → ℂ) q := by
  rw [← signedPlaneCoordinates_apply, signedPlaneCoordinates_inclusion]

theorem signedCoordinates_inclusion_opposite (p q : SignedPlaneIndex) (z : ℂ) :
    signedCoordinates (signedPlaneInclusion p z) (oppositeCharge q.val) = star ((Pi.single p z : SignedPlaneIndex → ℂ) q) := by
  rw [signedCoordinates_opposite, signedCoordinates_inclusion_representative]

theorem signedPlaneInclusion_injective (p : SignedPlaneIndex) :
    Function.Injective (signedPlaneInclusion p) := by
  intro z w h
  have hcoord := congrArg (fun x ↦ signedPlaneCoordinates x p) h
  simpa only [signedPlaneCoordinates_inclusion, Pi.single_eq_same] using hcoord

/-- The coordinate plane as a real submodule of the actual signed carrier. -/
def signedPlane (p : SignedPlaneIndex) : Submodule ℝ SignedField :=
  LinearMap.range (signedPlaneInclusion p)

theorem mem_signedPlane_iff {p : SignedPlaneIndex} {x : SignedField} :
    x ∈ signedPlane p ↔ ∀ q ≠ p, signedPlaneCoordinates x q = 0 := by
  constructor
  · rintro ⟨z, rfl⟩ q hq
    rw [signedPlaneCoordinates_inclusion, Pi.single_eq_of_ne hq]
  · intro h
    refine ⟨signedPlaneCoordinates x p, signedPlaneCoordinates.injective ?_⟩
    rw [signedPlaneCoordinates_inclusion]
    funext q
    by_cases hq : q = p
    · subst q
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hq, h q hq]

/-- A signed plane is a complex coordinate viewed as a real vector space. -/
def signedPlaneEquiv (p : SignedPlaneIndex) : ℂ ≃ₗ[ℝ] signedPlane p :=
  LinearEquiv.ofInjective (signedPlaneInclusion p) (signedPlaneInclusion_injective p)

theorem signedPlane_finrank (p : SignedPlaneIndex) : Module.finrank ℝ (signedPlane p) = 2 := by
  rw [← (signedPlaneEquiv p).finrank_eq, Complex.finrank_real_complex]

theorem signedPlane_pairwise_orthogonal :
    Pairwise (fun p q : SignedPlaneIndex ↦ (signedPlane p).IsOrtho (signedPlane q)) := by
  intro p q hpq
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
  apply (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
    (signedPlaneInclusion p z) (signedPlaneInclusion q w)).mp
  simp only [← pow_two, signedField_norm_sq_representatives, map_add, Pi.add_apply,
    signedPlaneCoordinates_inclusion]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = p
  · subst i
    simp [Pi.single_eq_of_ne hpq]
  · simp [Pi.single_eq_of_ne hi]

theorem signedPlane_sum (x : SignedField) :
    (∑ p, signedPlaneInclusion p (signedPlaneCoordinates x p)) = x := by
  apply signedPlaneCoordinates.injective
  rw [map_sum]
  simpa only [signedPlaneCoordinates_inclusion] using
    LinearMap.sum_single_apply (fun _ : SignedPlaneIndex ↦ ℂ) (signedPlaneCoordinates x)

theorem signedPlane_iSup_eq_top : (⨆ p, signedPlane p) = ⊤ := by
  apply top_unique
  intro x _
  rw [← signedPlane_sum x]
  exact Submodule.sum_mem _ (fun p _ ↦ (le_iSup signedPlane p) ⟨_, rfl⟩)

/-- The orthogonal projection onto a signed plane keeps exactly that complex coordinate. -/
theorem signedPlane_starProjection_apply (p : SignedPlaneIndex) (x : SignedField) :
    (signedPlane p).starProjection x = signedPlaneInclusion p (signedPlaneCoordinates x p) := by
  apply (signedPlane p).eq_starProjection_of_mem_orthogonal
  · exact ⟨_, rfl⟩
  · have h := Finset.sum_erase_add Finset.univ
        (fun q ↦ signedPlaneInclusion q (signedPlaneCoordinates x q)) (Finset.mem_univ p)
    rw [signedPlane_sum] at h
    rw [← eq_sub_iff_add_eq.mpr h]
    apply Submodule.sum_mem
    intro q hq
    exact signedPlane_pairwise_orthogonal (Finset.ne_of_mem_erase hq) ⟨_, rfl⟩

end

end ThirteenPlanes
