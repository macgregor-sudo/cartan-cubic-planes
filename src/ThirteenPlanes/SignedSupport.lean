module

public import ThirteenPlanes.Contracts
public import ThirteenPlanes.SignedPair
public import ThirteenPlanes.SignedPlanes
public import Mathlib.Data.Finset.Powerset

@[expose] public section

set_option backward.privateInPublic true

/-! The projective incidence and cubic support of the signed ternary model. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

/-- The signed carrier's actual orthogonal decomposition, for the contraction interface. -/
def signedPlaneDecomposition : PlaneDecomposition SignedField SignedPlaneIndex where
  plane := signedPlane
  dimension := signedPlane_finrank
  pairwise_orthogonal := signedPlane_pairwise_orthogonal
  exhaustive := signedPlane_iSup_eq_top

@[simp] theorem signedPlaneDecomposition_proj (p : SignedPlaneIndex) (x : SignedField) :
    signedPlaneDecomposition.proj p x = signedPlaneInclusion p (signedPlaneCoordinates x p) :=
  signedPlane_starProjection_apply p x

/-- Dot product over the charge field, using the three declared charges. -/
def chargeDot (x y : Charge) : ZMod 3 := ∑ i, x i * y i

theorem chargeDot_neg_left (x y : Charge) : chargeDot (-x) y = -chargeDot x y := by
  simp [chargeDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- The linear functional determined by a charge normal. -/
def chargeLinearDot (normal : Charge) : Charge →ₗ[ZMod 3] ZMod 3 where
  toFun := chargeDot normal
  map_add' x y := by simp [chargeDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [chargeDot, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ mul_left_comm _ _ _)

@[simp] theorem chargeLinearDot_apply (normal x : Charge) :
    chargeLinearDot normal x = chargeDot normal x := rfl

@[simp] theorem chargeDot_single (normal : Charge) (i : Fin 3) :
    chargeDot normal (Pi.single i 1) = normal i := by
  unfold chargeDot
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · simp

private theorem chargeLinearDot_ne_zero (normal : NonzeroCharge) :
    chargeLinearDot normal.val ≠ 0 := by
  intro h
  apply normal.property
  funext i
  have hi := LinearMap.congr_fun h (Pi.single i 1)
  simpa using hi

private theorem charge_finrank : Module.finrank (ZMod 3) Charge = 3 := by
  rw [Module.finrank_pi, Fintype.card_fin]

/-- A projective line is the two-dimensional charge subspace with a specified normal. -/
def signedProjectiveLine (l : SignedPlaneIndex) : Submodule (ZMod 3) Charge :=
  LinearMap.ker (chargeLinearDot l.val.val)

theorem signedProjectiveLine_finrank (l : SignedPlaneIndex) :
    Module.finrank (ZMod 3) (signedProjectiveLine l) = 2 := by
  have hs := surjective_of_ne_zero_of_finrank_eq_one (Module.finrank_self (ZMod 3))
    (chargeLinearDot_ne_zero l.val)
  have h := (chargeLinearDot l.val.val).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self, charge_finrank] at h
  unfold signedProjectiveLine
  omega

private theorem chargeLinearMap_eq (f : Charge →ₗ[ZMod 3] ZMod 3) :
    f = chargeLinearDot (fun i ↦ f (Pi.single i 1)) := by
  apply LinearMap.ext
  intro x
  calc
    f x = f (∑ i, Pi.single i (x i)) := by
      rw [LinearMap.sum_single_apply (fun _ : Fin 3 ↦ ZMod 3)]
    _ = chargeLinearDot (fun i ↦ f (Pi.single i 1)) x := by
      rw [map_sum, chargeLinearDot_apply, chargeDot]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi : (Pi.single i (x i) : Charge) = x i • Pi.single i 1 := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne hji]
      rw [hi, map_smul]
      exact mul_comm _ _

/-- Every two-dimensional subspace occurs among the projective line labels. -/
theorem exists_signedProjectiveLine_eq (U : Submodule (ZMod 3) Charge)
    (hU : Module.finrank (ZMod 3) U = 2) : ∃ l, signedProjectiveLine l = U := by
  have hlt : U < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro he
    rw [he, finrank_top, charge_finrank] at hU
    omega
  obtain ⟨f, hf, hker⟩ := U.exists_le_ker_of_lt_top hlt
  let normal : Charge := fun i ↦ f (Pi.single i 1)
  have hnormal : normal ≠ 0 := by
    intro hn
    apply hf
    rw [chargeLinearMap_eq f]
    change chargeLinearDot normal = 0
    rw [hn]
    apply LinearMap.ext
    intro x
    simp [chargeDot]
  obtain ⟨⟨l, sign⟩, hl⟩ := signedPlaneGradeEquiv.surjective ⟨normal, hnormal⟩
  have hle : U ≤ signedProjectiveLine l := by
    intro x hx
    have hx₀ : f x = 0 := LinearMap.mem_ker.mp (hker hx)
    rw [chargeLinearMap_eq f, chargeLinearDot_apply] at hx₀
    change chargeDot normal x = 0 at hx₀
    have he := congrArg Subtype.val hl
    cases sign
    · change l.val.val = normal at he
      exact LinearMap.mem_ker.mpr (by simpa only [chargeLinearDot_apply, he] using hx₀)
    · change -l.val.val = normal at he
      rw [← he, chargeDot_neg_left, neg_eq_zero] at hx₀
      exact LinearMap.mem_ker.mpr hx₀
  exact ⟨l, (Submodule.eq_of_le_of_finrank_eq hle (hU.trans (signedProjectiveLine_finrank l).symm)).symm⟩

/-- A normal line label denotes the projective points orthogonal to its representative. -/
def signedPointOnLine (p l : SignedPlaneIndex) : Prop := chargeDot l.val.val p.val.val = 0

instance : DecidableRel signedPointOnLine := fun p l ↦
  inferInstanceAs (Decidable (chargeDot l.val.val p.val.val = 0))

/-- Incidence of three points with a common projective line. -/
def signedCollinear (p q r : SignedPlaneIndex) : Prop :=
  ∃ l : SignedPlaneIndex, signedPointOnLine p l ∧ signedPointOnLine q l ∧ signedPointOnLine r l

theorem signedCollinear_iff_exists_twoDimensional (p q r : SignedPlaneIndex) :
    signedCollinear p q r ↔ ∃ U : Submodule (ZMod 3) Charge,
      Module.finrank (ZMod 3) U = 2 ∧ p.val.val ∈ U ∧ q.val.val ∈ U ∧ r.val.val ∈ U := by
  constructor
  · rintro ⟨l, hp, hq, hr⟩
    exact ⟨signedProjectiveLine l, signedProjectiveLine_finrank l,
      LinearMap.mem_ker.mpr hp, LinearMap.mem_ker.mpr hq, LinearMap.mem_ker.mpr hr⟩
  · rintro ⟨U, hU, hp, hq, hr⟩
    obtain ⟨l, rfl⟩ := exists_signedProjectiveLine_eq U hU
    exact ⟨l, LinearMap.mem_ker.mp hp, LinearMap.mem_ker.mp hq, LinearMap.mem_ker.mp hr⟩

instance (p q r : SignedPlaneIndex) : Decidable (signedCollinear p q r) :=
  inferInstanceAs (Decidable (∃ l : SignedPlaneIndex,
    signedPointOnLine p l ∧ signedPointOnLine q l ∧ signedPointOnLine r l))

/-- The four point labels on a projective line. -/
def signedLinePoints (l : SignedPlaneIndex) : Finset SignedPlaneIndex :=
  Finset.univ.filter (fun p ↦ signedPointOnLine p l)

/-- The unordered triples, each represented by a three-element set of point labels. -/
def signedCollinearTriples : Finset (Finset SignedPlaneIndex) :=
  Finset.univ.biUnion fun l ↦ (signedLinePoints l).powersetCard 3

theorem signedLinePoints_card : ∀ l : SignedPlaneIndex, (signedLinePoints l).card = 4 := by
  decide

theorem signedLineTriples_card (l : SignedPlaneIndex) :
    ((signedLinePoints l).powersetCard 3).card = 4 := by
  rw [Finset.card_powersetCard, signedLinePoints_card]
  decide

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem signedCollinearTriples_card : signedCollinearTriples.card = 52 := by
  decide

theorem mem_signedCollinearTriples_iff (p q r : SignedPlaneIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ({p, q, r} : Finset SignedPlaneIndex) ∈ signedCollinearTriples ↔ signedCollinear p q r := by
  have hcard : ({p, q, r} : Finset SignedPlaneIndex).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr])]
    simp
  simp [signedCollinearTriples, signedLinePoints, signedCollinear, Finset.mem_powersetCard,
    Finset.insert_subset_iff, hcard]

/-- The grade selected from a projective plane by a Boolean sign. -/
def signedGrade (p : SignedPlaneIndex) (sign : Bool) : NonzeroCharge :=
  signedPlaneGradeEquiv (p, sign)

@[simp] theorem signedGrade_false (p : SignedPlaneIndex) : signedGrade p false = p.val := rfl

@[simp] theorem signedGrade_true (p : SignedPlaneIndex) :
    signedGrade p true = oppositeCharge p.val := rfl

@[simp] theorem signedGrade_not (p : SignedPlaneIndex) (sign : Bool) :
    signedGrade p (!sign) = oppositeCharge (signedGrade p sign) := by
  cases sign <;> simp

/-- A zero-sum choice of grades after fixing the first of the three signs. -/
def signedCompletesZero (p q r : SignedPlaneIndex) (signs : Bool × Bool) : Prop :=
  p.val.val + (signedGrade q signs.1).val + (signedGrade r signs.2).val = 0

instance (p q r : SignedPlaneIndex) (signs : Bool × Bool) :
    Decidable (signedCompletesZero p q r signs) :=
  inferInstanceAs (Decidable (p.val.val + (signedGrade q signs.1).val +
    (signedGrade r signs.2).val = 0))

private def signedCompletions (p q r : SignedPlaneIndex) : Finset (Bool × Bool) :=
  Finset.univ.filter (signedCompletesZero p q r)

private theorem mem_signedCompletions (p q r : SignedPlaneIndex) (s : Bool × Bool) :
    s ∈ signedCompletions p q r ↔ signedCompletesZero p q r s := by
  simp [signedCompletions]

private def CollinearCompletionCheck (p q r : SignedPlaneIndex) : Prop :=
  (p ≠ q ∧ p ≠ r ∧ q ≠ r) →
    (signedCollinear p q r ↔ 0 < (signedCompletions p q r).card) ∧
    (signedCompletions p q r).card ≤ 1

private instance (p q r : SignedPlaneIndex) : Decidable (CollinearCompletionCheck p q r) := by
  unfold CollinearCompletionCheck
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem collinear_completion_check (p q r : SignedPlaneIndex) : CollinearCompletionCheck p q r := by
  have h : ∀ qr : SignedPlaneIndex × SignedPlaneIndex, CollinearCompletionCheck p qr.1 qr.2 := by
    fin_cases p <;> decide
  exact h (q, r)

private theorem collinear_completion_card (p q r : SignedPlaneIndex)
    (h : p ≠ q ∧ p ≠ r ∧ q ≠ r) :
    signedCollinear p q r ↔ (signedCompletions p q r).card = 1 := by
  obtain ⟨hiff, hle⟩ := collinear_completion_check p q r h
  rw [hiff]
  omega

private theorem signedCollinear_of_completion (p q r : SignedPlaneIndex)
    (h : p ≠ q ∧ p ≠ r ∧ q ≠ r) (s : Bool × Bool)
    (hs : signedCompletesZero p q r s) : signedCollinear p q r := by
  apply (collinear_completion_check p q r h).1.mpr
  exact Finset.card_pos.mpr ⟨s, (mem_signedCompletions p q r s).mpr hs⟩

/-- A collinear triple of distinct points admits exactly one signed completion fixing the first sign. -/
theorem signedCollinear_iff_unique_completion (p q r : SignedPlaneIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    signedCollinear p q r ↔ ∃ s : Bool × Bool,
      signedCompletesZero p q r s ∧ ∀ t, signedCompletesZero p q r t → t = s := by
  rw [collinear_completion_card p q r ⟨hpq, hpr, hqr⟩, Finset.card_eq_one]
  have hmem (s : Bool × Bool) :
      s ∈ signedCompletions p q r ↔ signedCompletesZero p q r s := by
    simp [signedCompletions]
  constructor
  · rintro ⟨s, h⟩
    refine ⟨s, (hmem s).mp (h.symm ▸ Finset.mem_singleton_self s), ?_⟩
    intro t ht
    simpa only [h, Finset.mem_singleton] using (hmem t).mpr ht
  · rintro ⟨s, hs, hu⟩
    refine ⟨s, Finset.ext fun x ↦ ?_⟩
    rw [Finset.mem_singleton, hmem]
    exact ⟨hu x, fun h ↦ h ▸ hs⟩

@[simp] theorem chargeRoot_re : chargeRoot.re = -1 / 2 := by
  norm_num [chargeRoot, Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

@[simp] theorem chargeRoot_im : chargeRoot.im = Real.sqrt 3 / 2 := by
  norm_num [chargeRoot, Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

theorem chargeRoot_ne_zero : chargeRoot ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp at he

/-- The conjugate of the specified primitive cube root is its square. -/
theorem chargeRoot_sq_eq_star : chargeRoot ^ 2 = star chargeRoot := by
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, chargeRoot_re, chargeRoot_im, Complex.star_def,
      Complex.conj_re]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · simp only [pow_two, Complex.mul_im, chargeRoot_re, chargeRoot_im, Complex.star_def,
      Complex.conj_im]
    ring

private theorem chargeRoot_pow_neg (e : ZMod 3) :
    chargeRoot ^ (-e).val = star (chargeRoot ^ e.val) := by
  fin_cases e
  · change chargeRoot ^ 0 = star (chargeRoot ^ 0)
    simp
  · change chargeRoot ^ 2 = star (chargeRoot ^ 1)
    simpa only [pow_one] using chargeRoot_sq_eq_star
  · change chargeRoot ^ 1 = star (chargeRoot ^ 2)
    rw [chargeRoot_sq_eq_star, star_star, pow_one]

private theorem gradedProductCoefficient_neg (x y : Charge) :
    gradedProductCoefficient (-x) (-y) = star (gradedProductCoefficient x y) := by
  have hdep : dependentGrades (-x) (-y) ↔ dependentGrades x y := by
    simp [dependentGrades, neg_eq_iff_eq_neg]
  have hexp : gradeExponent (-x) (-y) = -gradeExponent x y := by
    simp only [gradeExponent, Pi.neg_apply]
    ring
  by_cases h : dependentGrades x y
  · simp [gradedProductCoefficient, hdep, h]
  · simp [gradedProductCoefficient, hdep, h, hexp, chargeRoot_pow_neg]

theorem signedCoefficient_opposite (x y z : NonzeroCharge) :
    signedCoefficient (oppositeCharge x) (oppositeCharge y) (oppositeCharge z) =
      star (signedCoefficient x y z) := by
  unfold signedCoefficient
  change gradedProductCoefficient (-x.val) (-y.val) * gradeMetric (-x.val + -y.val) (-z.val) = _
  rw [gradedProductCoefficient_neg, star_mul, mul_comm (star (gradeMetric _ _))]
  congr 1
  rw [← neg_add]
  unfold gradeMetric
  have hneg : -(x.val + y.val) + -z.val = 0 ↔ x.val + y.val + z.val = 0 := by
    rw [← neg_add, neg_eq_zero]
  simp only [hneg]
  split_ifs <;> norm_num

theorem signedCoefficient_ne_zero_of_grade_sum_zero (x y z : NonzeroCharge)
    (h : x.val + y.val + z.val = 0) : signedCoefficient x y z ≠ 0 := by
  by_cases hd : dependentGrades x.val y.val <;>
    simp [signedCoefficient, gradeMetric, h, gradedProductCoefficient, hd, chargeRoot_ne_zero]

/-- The complex coordinate belonging to the selected sign of a representative grade. -/
def signedGradeCoordinate (s : Bool) (z : ℂ) : ℂ := if s then star z else z

private theorem signedGradeCoordinate_not (s : Bool) (z : ℂ) : signedGradeCoordinate (!s) z = star (signedGradeCoordinate s z) := by
  cases s <;> simp [signedGradeCoordinate]

private theorem sum_signedPlaneInclusion (p : SignedPlaneIndex) (z : ℂ)
    (f : NonzeroCharge → ℂ → ℝ) (h₀ : ∀ i, f i 0 = 0) :
    (∑ i, f i (signedCoordinates (signedPlaneInclusion p z) i)) =
      ∑ s : Bool, f (signedGrade p s) (signedGradeCoordinate s z) := by
  rw [← signedPlaneGradeEquiv.sum_comp (fun i ↦ f i (signedCoordinates (signedPlaneInclusion p z) i)),
    Fintype.sum_prod_type, Finset.sum_eq_single p]
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    cases s
    · simp [signedGrade, signedGradeCoordinate, signedCoordinates_inclusion_representative]
    · simp [signedGrade, signedGradeCoordinate, signedCoordinates_inclusion_representative]
  · intro q _ hqp
    apply Finset.sum_eq_zero
    intro s _
    cases s
    · simp [signedCoordinates_inclusion_representative, Pi.single_eq_of_ne hqp, h₀]
    · simp [signedCoordinates_inclusion_representative, Pi.single_eq_of_ne hqp, h₀]
  · simp

private def planeSummand (p q r : SignedPlaneIndex) (x y z : ℂ) (i j k : Bool) : ℝ :=
  (signedCoefficient (signedGrade p i) (signedGrade q j) (signedGrade r k) *
    signedGradeCoordinate i x * signedGradeCoordinate j y * signedGradeCoordinate k z).re

private theorem planeSummand_not (p q r : SignedPlaneIndex) (x y z : ℂ) (i j k : Bool) :
    planeSummand p q r x y z (!i) (!j) (!k) = planeSummand p q r x y z i j k := by
  simp only [planeSummand, signedGrade_not, signedCoefficient_opposite, signedGradeCoordinate_not,
    Complex.star_def, ← map_mul, Complex.conj_re]

set_option maxHeartbeats 600000 in
/-- Evaluating the cubic on three coordinate planes reduces to four possible sign choices. -/
theorem signedEqualCubic_on_plane_inclusions (p q r : SignedPlaneIndex) (x y z : ℂ) :
    signedEqualCubic.apply (signedPlaneInclusion p x) (signedPlaneInclusion q y)
      (signedPlaneInclusion r z) =
      2 * ∑ s : Bool × Bool,
        (signedCoefficient p.val (signedGrade q s.1) (signedGrade r s.2) * x *
          signedGradeCoordinate s.1 y * signedGradeCoordinate s.2 z).re := by
  have hsum : signedEqualCubic.apply (signedPlaneInclusion p x) (signedPlaneInclusion q y)
      (signedPlaneInclusion r z) = ∑ i, ∑ j, ∑ k, planeSummand p q r x y z i j k := by
    rw [signedEqualCubic_apply]
    let yp := signedPlaneInclusion q y
    let zp := signedPlaneInclusion r z
    let f₁ (i : NonzeroCharge) (a : ℂ) := ∑ j, ∑ k,
      (signedCoefficient i j k * a * signedCoordinates yp j * signedCoordinates zp k).re
    refine (sum_signedPlaneInclusion p x f₁ (fun i ↦ by simp [f₁])).trans ?_
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    let f₂ (j : NonzeroCharge) (b : ℂ) := ∑ k,
      (signedCoefficient (signedGrade p i) j k * signedGradeCoordinate i x * b * signedCoordinates zp k).re
    refine (sum_signedPlaneInclusion q y f₂ (fun j ↦ by simp [f₂])).trans ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact sum_signedPlaneInclusion r z
      (fun k w ↦ (signedCoefficient (signedGrade p i) (signedGrade q j) k *
        signedGradeCoordinate i x * signedGradeCoordinate j y * w).re) (fun _ ↦ by simp)
  have hpair : (∑ j, ∑ k, planeSummand p q r x y z true j k) =
      ∑ j, ∑ k, planeSummand p q r x y z false j k := by
    have h₁ : planeSummand p q r x y z true true true = planeSummand p q r x y z false false false :=
      planeSummand_not p q r x y z false false false
    have h₂ : planeSummand p q r x y z true true false = planeSummand p q r x y z false false true :=
      planeSummand_not p q r x y z false false true
    have h₃ : planeSummand p q r x y z true false true = planeSummand p q r x y z false true false :=
      planeSummand_not p q r x y z false true false
    have h₄ : planeSummand p q r x y z true false false = planeSummand p q r x y z false true true :=
      planeSummand_not p q r x y z false true true
    simp only [Fintype.sum_bool, h₁, h₂, h₃, h₄]
    abel
  rw [hsum, Fintype.sum_bool, hpair, ← two_mul, Fintype.sum_prod_type]
  rfl

private theorem signedCoefficient_zero_of_not_completion (p q r : SignedPlaneIndex) (s : Bool × Bool)
    (h : ¬ signedCompletesZero p q r s) :
    signedCoefficient p.val (signedGrade q s.1) (signedGrade r s.2) = 0 :=
  signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ h

/-- A distinct triple of actual real planes supports the cubic exactly when it is collinear. -/
theorem signedEqualCubic_plane_support_iff_collinear (p q r : SignedPlaneIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∃ (x : signedPlane p) (y : signedPlane q) (z : signedPlane r),
      signedEqualCubic.apply x y z ≠ 0) ↔ signedCollinear p q r := by
  constructor
  · rintro ⟨⟨_, ⟨x, rfl⟩⟩, ⟨_, ⟨y, rfl⟩⟩, ⟨_, ⟨z, rfl⟩⟩, h⟩
    rw [signedEqualCubic_on_plane_inclusions] at h
    by_contra hn
    have hg (s : Bool × Bool) : ¬ signedCompletesZero p q r s :=
      fun hs ↦ hn (signedCollinear_of_completion p q r ⟨hpq, hpr, hqr⟩ s hs)
    apply h
    simp [signedCoefficient_zero_of_not_completion, hg]
  · intro h
    obtain ⟨s, hs, hu⟩ := (signedCollinear_iff_unique_completion p q r hpq hpr hqr).mp h
    let c := signedCoefficient p.val (signedGrade q s.1) (signedGrade r s.2)
    have hc : c ≠ 0 := signedCoefficient_ne_zero_of_grade_sum_zero _ _ _ hs
    refine ⟨⟨signedPlaneInclusion p (star c), ⟨_, rfl⟩⟩,
      ⟨signedPlaneInclusion q 1, ⟨_, rfl⟩⟩,
      ⟨signedPlaneInclusion r 1, ⟨_, rfl⟩⟩, ?_⟩
    rw [signedEqualCubic_on_plane_inclusions, Finset.sum_eq_single s]
    · have hn : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
      have hsign (d : Bool) : signedGradeCoordinate d 1 = 1 := by cases d <;> simp [signedGradeCoordinate]
      change 2 * (c * star c * signedGradeCoordinate s.1 1 * signedGradeCoordinate s.2 1).re ≠ 0
      simp only [hsign, mul_one, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact ne_of_gt (mul_pos (by norm_num) hn)
    · intro t _ ht
      have hn : ¬ signedCompletesZero p q r t := fun hd ↦ ht (hu t hd)
      simp [signedCoefficient_zero_of_not_completion, hn]
    · simp

private theorem signedGrade_eq_iff (p q : SignedPlaneIndex) (s t : Bool) :
    signedGrade p s = signedGrade q t ↔ p = q ∧ s = t := by
  change signedPlaneGradeEquiv (p, s) = signedPlaneGradeEquiv (q, t) ↔ _
  rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]

private theorem signedCoefficient_repeat_plane (p q : SignedPlaneIndex) (s t : Bool) :
    signedCoefficient p.val (signedGrade p s) (signedGrade q t) =
      if p = q ∧ s = false ∧ t = false then 3 else 0 := by
  cases s
  · rw [signedGrade_false, signedCoefficient_repeated_first]
    have he : p.val = signedGrade q t ↔ p = q ∧ t = false := by
      rw [← signedGrade_false p, signedGrade_eq_iff]
      simp [eq_comm]
    simp [signedDiagonalCoefficient, he]
  · have hn : p.val.val + (signedGrade p true).val + (signedGrade q t).val ≠ 0 := by
      simpa [signedGrade_true, oppositeCharge] using (signedGrade q t).property
    rw [signedCoefficient_zero_of_grade_sum_ne_zero _ _ _ hn]
    simp

/-- On an individual plane the real polar form is the diagonal cubic of coefficient six. -/
theorem signedEqualCubic_on_same_plane (p : SignedPlaneIndex) (x y z : ℂ) :
    signedEqualCubic.apply (signedPlaneInclusion p x) (signedPlaneInclusion p y)
      (signedPlaneInclusion p z) = 6 * (x * y * z).re := by
  rw [signedEqualCubic_on_plane_inclusions, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, signedCoefficient_repeat_plane, and_self, eq_self, true_and,
    Bool.true_eq_false, false_and, and_false, ↓reduceIte, zero_mul, Complex.zero_re,
    zero_add, signedGradeCoordinate, Bool.false_eq_true]
  rw [show (3 : ℂ) * x * y * z = 3 * (x * y * z) by ring, Complex.mul_re]
  norm_num
  ring

/-- A term with two fields on one plane and a third on a distinct plane vanishes. -/
theorem signedEqualCubic_on_exactly_two_planes {p q : SignedPlaneIndex} (hpq : p ≠ q)
    (x y z : ℂ) :
    signedEqualCubic.apply (signedPlaneInclusion p x) (signedPlaneInclusion p y)
      (signedPlaneInclusion q z) = 0 := by
  rw [signedEqualCubic_on_plane_inclusions]
  simp [signedCoefficient_repeat_plane, hpq]

theorem signedEqualCubic_repeatedPlane (p : SignedPlaneIndex) (x y : signedPlane p)
    (z : (signedPlane p)ᗮ) : signedEqualCubic.apply x y z = 0 := by
  rcases x with ⟨_, ⟨x, rfl⟩⟩
  rcases y with ⟨_, ⟨y, rfl⟩⟩
  have hproj : (signedPlane p).starProjection z = 0 := by
    apply (signedPlane p).eq_starProjection_of_mem_orthogonal (zero_mem _)
    rw [sub_zero]
    exact z.property
  have hz : signedPlaneCoordinates (z : SignedField) p = 0 := by
    apply signedPlaneInclusion_injective p
    simpa only [signedPlane_starProjection_apply, map_zero] using hproj
  let f := signedEqualCubic.trilinear (signedPlaneInclusion p x) (signedPlaneInclusion p y)
  calc
    _ = f (z : SignedField) := (SymmetricCubic.trilinear_apply _ _ _ _).symm
    _ = f (∑ q, signedPlaneInclusion q (signedPlaneCoordinates z q)) :=
      congrArg f (signedPlane_sum z).symm
    _ = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun q _ ↦ ?_
      by_cases hpq : p = q
      · subst q
        rw [hz, map_zero, map_zero]
      · calc
          _ = signedEqualCubic.apply (signedPlaneInclusion p x) (signedPlaneInclusion p y)
                (signedPlaneInclusion q (signedPlaneCoordinates z q)) :=
            SymmetricCubic.trilinear_apply _ _ _ _
          _ = 0 := signedEqualCubic_on_exactly_two_planes hpq _ _ _

theorem signedDiagonalCubic_rep_sum (x y z : SignedField) :
    signedDiagonalCubic.apply x y z = 6 * ∑ p,
      (signedPlaneCoordinates x p * signedPlaneCoordinates y p * signedPlaneCoordinates z p).re := by
  classical
  rw [signedDiagonalCubic_sum,
    ← signedPlaneGradeEquiv.sum_comp (fun i ↦
      (signedCoordinates x i * signedCoordinates y i * signedCoordinates z i).re),
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, signedPlaneGradeEquiv_true, signedPlaneGradeEquiv_false,
    signedCoordinates_opposite, Complex.star_def, ← map_mul, Complex.conj_re,
    ← signedPlaneCoordinates_apply, ← two_mul, ← Finset.mul_sum]
  ring

/-- The signed diagonal coupling is the sum of the thirteen pulled-back restrictions. -/
theorem signedPair_diagonal_eq_sum_restrictions :
    signedPair.diagonalCubic = ∑ p, (interactionCubic signedPair 1).pullback
      (signedPlaneDecomposition.proj p) := by
  apply SymmetricCubic.ext
  intro x y z
  rw [signedPair_at_one]
  change signedDiagonalCubic.apply x y z = _
  rw [signedDiagonalCubic_rep_sum]
  have hsum (f : SignedPlaneIndex → SymmetricCubic SignedField) :
      (∑ p, f p).apply x y z = ∑ p, (f p).apply x y z := by
    simp only [SymmetricCubic.apply, map_sum, LinearMap.sum_apply, sum_inner]
  rw [hsum, Finset.mul_sum]
  simp only [SymmetricCubic.pullback_apply, signedPlaneDecomposition_proj,
    signedEqualCubic_on_same_plane]

/-- The counted incidence triples are the support of the real cubic on distinct planes. -/
theorem mem_signedCollinearTriples_iff_cubic_support (p q r : SignedPlaneIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ({p, q, r} : Finset SignedPlaneIndex) ∈ signedCollinearTriples ↔
      ∃ (x : signedPlane p) (y : signedPlane q) (z : signedPlane r),
        signedEqualCubic.apply x y z ≠ 0 :=
  (mem_signedCollinearTriples_iff p q r hpq hpr hqr).trans
    (signedEqualCubic_plane_support_iff_collinear p q r hpq hpr hqr).symm

theorem signedPlaneInclusion_norm_sq (p : SignedPlaneIndex) (z : ℂ) :
    ‖signedPlaneInclusion p z‖ ^ 2 = 6 * ‖z‖ ^ 2 := by
  rw [signedField_norm_sq_representatives]
  simp only [signedPlaneCoordinates_inclusion]
  rw [Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro q _ hqp
    simp [Pi.single_eq_of_ne hqp]
  · simp

theorem signedPlaneInclusion_inner (p : SignedPlaneIndex) (z w : ℂ) :
    ⟪signedPlaneInclusion p z, signedPlaneInclusion p w⟫_ℝ = 6 * (star z * w).re := by
  have h := norm_add_sq_real (signedPlaneInclusion p z) (signedPlaneInclusion p w)
  rw [← (signedPlaneInclusion p).map_add] at h
  simp only [signedPlaneInclusion_norm_sq, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im] at h
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith only [h]

private theorem signedPlaneEquiv_coe (p : SignedPlaneIndex) (z : ℂ) :
    (signedPlaneEquiv p z : SignedField) = signedPlaneInclusion p z :=
  LinearEquiv.ofInjective_apply _ _

/-- Multiplication by a fixed field in a single plane is conjugate complex multiplication. -/
theorem signedPlane_restriction_L (p : SignedPlaneIndex) (x y : ℂ) :
    (signedPlaneDecomposition.restriction p signedEqualCubic).L
      (signedPlaneEquiv p x) (signedPlaneEquiv p y) = signedPlaneEquiv p (star (x * y)) := by
  apply ext_inner_right ℝ
  intro w
  obtain ⟨z, rfl⟩ := (signedPlaneEquiv p).surjective w
  have hc := signedPlaneDecomposition.restriction_apply p signedEqualCubic
    (signedPlaneEquiv p x) (signedPlaneEquiv p y) (signedPlaneEquiv p z)
  change ⟪_, _⟫_ℝ = _ at hc
  rw [hc]
  simp only [signedPlaneEquiv_coe]
  rw [signedEqualCubic_on_same_plane]
  change 6 * (x * y * z).re =
    ⟪(signedPlaneEquiv p (star (x * y)) : SignedField), (signedPlaneEquiv p z : SignedField)⟫_ℝ
  rw [signedPlaneEquiv_coe, signedPlaneEquiv_coe, signedPlaneInclusion_inner, star_star]

/-- The real two-dimensional slices of the single-plane cubic have trace zero. -/
theorem signedPlane_restriction_traceFree (p : SignedPlaneIndex) :
    (signedPlaneDecomposition.restriction p signedEqualCubic).TraceFree := by
  intro w
  obtain ⟨x, rfl⟩ := (signedPlaneEquiv p).surjective w
  let T : ℂ →ₗ[ℝ] ℂ :=
    Complex.conjAe.toLinearEquiv.toLinearMap.comp (LinearMap.mulLeft ℝ x)
  have hT (y : ℂ) : T y = star (x * y) := rfl
  have h : (signedPlaneDecomposition.restriction p signedEqualCubic).L (signedPlaneEquiv p x) =
      (signedPlaneEquiv p).conj T := by
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := (signedPlaneEquiv p).surjective y
    rw [signedPlane_restriction_L]
    change signedPlaneEquiv p (star (x * z)) =
      signedPlaneEquiv p (T ((signedPlaneEquiv p).symm (signedPlaneEquiv p z)))
    rw [LinearEquiv.symm_apply_apply, hT]
  rw [h]
  change LinearMap.trace ℝ (signedPlane p) ((signedPlaneEquiv p).conj T) = 0
  rw [LinearMap.trace_conj', LinearMap.trace_eq_matrix_trace ℝ Complex.basisOneI, Matrix.trace,
    Fin.sum_univ_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr, hT,
    Complex.mul_im]

/-- The geometric plane data consumed by the common tensor contraction proof. -/
theorem signedPair_hasPlaneData : HasPlaneData signedPair signedPlaneDecomposition where
  diagonal_eq := signedPair_diagonal_eq_sum_restrictions
  traceFree p := by rw [signedPair_at_one]; exact signedPlane_restriction_traceFree p
  repeatedPlane p x y z := by
    rw [signedPair_at_one]
    exact signedEqualCubic_repeatedPlane p x y z

end

end ThirteenPlanes
