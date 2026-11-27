module

public import ThirteenPlanes.Contracts
public import ThirteenPlanes.SignedPair
public import ThirteenPlanes.SignedTitsMetric
public import ThirteenPlanes.SignedTitsProduct
public import ThirteenPlanes.Tits.SquareLaw

@[expose] public section

set_option backward.privateInPublic true

open scoped Matrix RealInnerProductSpace BigOperators
open AlbertLean.Generic.C1Coordinates AlbertLean.Generic.TitsLinear AlbertLean.Generic.TitsSquare

namespace ThirteenPlanes

noncomputable section

private theorem chargeFrom_eq_iff (v : WeylLabel) (k : ZMod 3) (x : Charge) :
    chargeFrom v k = x ↔ v = (x 0, x 1) ∧ k = x 2 := by
  constructor
  · intro h
    exact ⟨Prod.ext (congrFun h 0) (congrFun h 1), congrFun h 2⟩
  · rintro ⟨rfl, rfl⟩
    exact chargeFrom_components x

private theorem component_homogeneous (x : Charge) (k : ZMod 3) :
    titsComponent (homogeneousTits x) k =
      if x 2 = k then (weylMatrix (x 0, x 1) : Mat3 ℂ) else 0 := by
  fin_cases k <;> rfl

/-- The complex charge coordinate vector with coefficient one at grade x. -/
def chargeBasisVector (x : Charge) : Charge → ℂ := fun y => if y = x then 1 else 0

/-- A single charge coefficient synthesizes to its homogeneous Weyl vector. -/
theorem gradedTitsCoordinates_single (x : Charge) :
    gradedTitsCoordinates (chargeBasisVector x) = homogeneousTits x := by
  apply titsComponent_injective
  funext k
  change titsComponent (gradedTitsCoordinates (chargeBasisVector x)) k =
    titsComponent (homogeneousTits x) k
  rw [titsComponent_gradedTitsCoordinates, component_homogeneous]
  change (∑ v : WeylLabel, chargeBasisVector x (chargeFrom v k) • weylMatrix v) = _
  simp only [chargeBasisVector, chargeFrom_eq_iff, ite_smul, one_smul, zero_smul]
  by_cases h : k = x 2
  · simp [h]
  · simp [h, Ne.symm h]

private theorem weylMatrix_zero : weylMatrix 0 = (1 : WeylMatrixSpace) := by
  ext i j
  simp [weylMatrix, Matrix.one_apply]

/-- The zero Weyl grade gives the named Tits unit. -/
@[simp] theorem gradedTitsCoordinates_unit :
    gradedTitsCoordinates (chargeBasisVector 0) = firstTitsOne := by
  rw [gradedTitsCoordinates_single]
  change ((weylMatrix 0 : Mat3 ℂ), 0, 0) = (1, 0, 0)
  exact Prod.ext weylMatrix_zero rfl

theorem gradedTitsCoordinates_sum (z : Charge → ℂ) :
    gradedTitsCoordinates z = ∑ x, z x • homogeneousTits x := by
  have hz : (∑ x : Charge, z x • chargeBasisVector x) = z := by
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, chargeBasisVector, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    simp
  calc
    gradedTitsCoordinates z = gradedTitsCoordinates (∑ x, z x • chargeBasisVector x) :=
      congrArg gradedTitsCoordinates hz.symm
    _ = _ := by simp only [map_sum, map_smul, gradedTitsCoordinates_single]

theorem titsTraceForm_homogeneous (x y : Charge) :
    titsTraceForm (homogeneousTits x) (homogeneousTits y) = gradeMetric x y := by
  rw [← gradedTitsCoordinates_single x, ← gradedTitsCoordinates_single y,
    gradedTitsCoordinates_traceForm]
  have h : -x = y ↔ x+y=0 := by
    constructor
    · intro e
      rw [← e, add_neg_cancel]
    · intro e
      exact (eq_neg_of_add_eq_zero_right e).symm
  simp only [chargeBasisVector, ite_mul, one_mul, zero_mul]
  simp [gradeMetric, h]

private def titsProductLinear : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ →ₗ[ℂ] FirstTits ℂ :=
  LinearMap.mk₂ ℂ (polarProduct firstTitsSquare)
    (by intros; apply toTau.injective; simp [toTau_polarProduct, add_mul])
    (by intros; apply toTau.injective; simp [toTau_polarProduct, smul_mul_assoc])
    (by intros; apply toTau.injective; simp [toTau_polarProduct, mul_add])
    (by intros; apply toTau.injective; simp [toTau_polarProduct, mul_smul_comm])

/-- The complete 27-grade product with its named unit at grade zero. -/
def gradedProduct (x y : Charge → ℂ) : Charge → ℂ :=
  ∑ i, ∑ j, (gradedProductCoefficient i j * x i * y j) • chargeBasisVector (i+j)

theorem gradedTitsComplexEquiv_product (x y : Charge → ℂ) :
    gradedTitsComplexEquiv (gradedProduct x y) =
      polarProduct firstTitsSquare (gradedTitsComplexEquiv x) (gradedTitsComplexEquiv y) := by
  change gradedTitsCoordinates (gradedProduct x y) =
    titsProductLinear (gradedTitsCoordinates x) (gradedTitsCoordinates y)
  simp only [gradedProduct, map_sum, map_smul, gradedTitsCoordinates_single]
  rw [gradedTitsCoordinates_sum x, gradedTitsCoordinates_sum y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have h : titsProductLinear (homogeneousTits i) (homogeneousTits j) =
      gradedProductCoefficient i j • homogeneousTits (i+j) := homogeneousTits_product i j
  rw [h, smul_smul, smul_smul]
  congr 1
  ring

private def titsTraceLinear : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ titsTraceForm
    (by intros; simp [titsTraceForm, add_mul, Tits.trace3_eq_matrixTrace]; ring)
    (by intros; simp [titsTraceForm, Tits.trace3_eq_matrixTrace,
      smul_eq_mul, mul_add])
    (by intros; simp [titsTraceForm, mul_add, Tits.trace3_eq_matrixTrace]; ring)
    (by intros; simp [titsTraceForm, Tits.trace3_eq_matrixTrace,
      smul_eq_mul, mul_add])

@[simp] private theorem titsProductLinear_apply (x y : FirstTits ℂ) :
    titsProductLinear x y = polarProduct firstTitsSquare x y := rfl

@[simp] private theorem titsTraceLinear_apply (x y : FirstTits ℂ) :
    titsTraceLinear x y = titsTraceForm x y := rfl

private theorem reverse_three_sums {A : Type*} [AddCommMonoid A] (f : Charge → Charge → Charge → A) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The trace tensor of the complex product in its marked Weyl basis. -/
theorem gradedTits_traceTensor (x y z : Charge → ℂ) :
    titsTraceForm (polarProduct firstTitsSquare (gradedTitsCoordinates x) (gradedTitsCoordinates y))
      (gradedTitsCoordinates z) =
      ∑ i, ∑ j, ∑ k, (gradedProductCoefficient i j * gradeMetric (i+j) k) * x i * y j * z k := by
  change titsTraceLinear (titsProductLinear (gradedTitsCoordinates x) (gradedTitsCoordinates y))
    (gradedTitsCoordinates z) = _
  rw [gradedTitsCoordinates_sum x, gradedTitsCoordinates_sum y, gradedTitsCoordinates_sum z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]
  conv_rhs => rw [reverse_three_sums]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  have hc : titsProductLinear (homogeneousTits k) (homogeneousTits j) =
      gradedProductCoefficient k j • homogeneousTits (k+j) := homogeneousTits_product k j
  rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, titsTraceLinear_apply,
    titsTraceForm_homogeneous]
  ring

private theorem charge_sum_nonzero {A : Type*} [AddCommMonoid A]
    (f : Charge → A) (hf : f 0 = 0) :
    ∑ q : Charge, f q = ∑ q : NonzeroCharge, f q.val := by
  classical
  calc
    _ = ∑ q ∈ (Finset.univ : Finset Charge) with q ≠ 0, f q := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hn
      have hq : q = 0 := by simpa using hn
      simpa only [hq] using hf
    _ = _ := by rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]

private theorem extendedCharge_traceTensor (x y z : SignedField) :
    (∑ i : Charge, ∑ j : Charge, ∑ k : Charge,
      (gradedProductCoefficient i j * gradeMetric (i+j) k) *
        signedExtend x i * signedExtend y j * signedExtend z k) =
    ∑ i : NonzeroCharge, ∑ j : NonzeroCharge, ∑ k : NonzeroCharge,
      signedCoefficient i j k * signedCoordinates x i * signedCoordinates y j * signedCoordinates z k := by
  rw [charge_sum_nonzero _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [charge_sum_nonzero _ (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [charge_sum_nonzero _ (by simp)]
  simp only [signedExtend_nonzero, signedCoefficient]

/-- The real signed cubic is the compact trace of the Jordan product. -/
theorem signedEqualCubic_tits (x y z : SignedField) :
    signedEqualCubic.apply x y z =
      ⟪Tits.CompactTits.product (gradedTitsEquiv x).val (gradedTitsEquiv y).val,
        (gradedTitsEquiv z).val⟫ := by
  rw [Tits.CompactTits.inner_eq_complexTrace_re]
  change signedEqualCubic.apply x y z =
    (titsTraceForm
      (Tits.CompactTits.coordinates
        (Tits.CompactTits.product (gradedTitsEquiv x).val (gradedTitsEquiv y).val))
      (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv z))).re
  rw [Tits.CompactTits.coordinates_product_eq_polar]
  change signedEqualCubic.apply x y z =
    (titsTraceForm (polarProduct firstTitsSquare
      (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv x))
      (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv y)))
      (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv z))).re
  rw [gradedTitsEquiv_coordinates, gradedTitsEquiv_coordinates, gradedTitsEquiv_coordinates,
    gradedTits_traceTensor, extendedCharge_traceTensor, signedEqualCubic_re_sum]

/-- The unprojected complex coefficient sum already lies in the real form. -/
theorem signedTraceTensor_real (x y z : SignedField) :
    ((signedEqualCubic.apply x y z : ℝ) : ℂ) =
      ∑ i : NonzeroCharge, ∑ j : NonzeroCharge, ∑ k : NonzeroCharge,
        signedCoefficient i j k * signedCoordinates x i * signedCoordinates y j * signedCoordinates z k := by
  rw [signedEqualCubic_tits, Tits.CompactTits.complexTrace_eq_inner]
  change titsTraceForm
    (Tits.CompactTits.coordinates
      (Tits.CompactTits.product (gradedTitsEquiv x).val (gradedTitsEquiv y).val))
    (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv z)) = _
  rw [Tits.CompactTits.coordinates_product_eq_polar]
  change titsTraceForm (polarProduct firstTitsSquare
    (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv x))
    (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv y)))
    (Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv z)) = _
  rw [gradedTitsEquiv_coordinates, gradedTitsEquiv_coordinates, gradedTitsEquiv_coordinates,
    gradedTits_traceTensor, extendedCharge_traceTensor]

theorem signedTraceTensor_im_eq_zero (x y z : SignedField) :
    (∑ i : NonzeroCharge, ∑ j : NonzeroCharge, ∑ k : NonzeroCharge,
      signedCoefficient i j k * signedCoordinates x i * signedCoordinates y j * signedCoordinates z k).im = 0 := by
  rw [← signedTraceTensor_real, Complex.ofReal_im]

theorem compactTitsProduct_self (x : Tits.CompactTits) :
    Tits.CompactTits.product x x = Tits.CompactTits.square x := by
  apply Tits.CompactTits.ext
  rw [Tits.CompactTits.coordinates_product_eq_polar, Tits.CompactTits.coordinates_square]
  exact toTau.injective (by rw [toTau_polarProduct, toTau_firstTitsSquare])

/-- Raising an index of the signed tensor gives the compact traceless Jordan product. -/
theorem gradedTitsEquiv_signedProduct (x y : SignedField) :
    gradedTitsEquiv (signedEqualCubic.L x y) =
      Tits.CompactTits.center
        (Tits.CompactTits.product (gradedTitsEquiv x).val (gradedTitsEquiv y).val) := by
  apply ext_inner_right ℝ
  intro v
  obtain ⟨z, rfl⟩ := gradedTitsEquiv.surjective v
  rw [gradedTitsEquiv.inner_map_map]
  change signedEqualCubic.apply x y z = _
  rw [signedEqualCubic_tits]
  let p := Tits.CompactTits.product (gradedTitsEquiv x).val (gradedTitsEquiv y).val
  change ⟪p, (gradedTitsEquiv z).val⟫ =
    ⟪p - (Tits.CompactTits.trace p / 3) • Tits.CompactTits.one, (gradedTitsEquiv z).val⟫
  rw [inner_sub_left, real_inner_smul_left, real_inner_comm (gradedTitsEquiv z).val Tits.CompactTits.one,
    Tits.CompactTits.inner_one_right, Tits.CompactTitsTraceless.trace_zero, mul_zero, sub_zero]

/-- The raised square of the signed tensor is the full centered Jordan square. -/
theorem gradedTitsEquiv_signedSquare (x : SignedField) :
    gradedTitsEquiv (signedEqualCubic.squareMap x) =
      Tits.CompactTitsTraceless.square (gradedTitsEquiv x) := by
  rw [SymmetricCubic.squareMap, gradedTitsEquiv_signedProduct, compactTitsProduct_self,
    Tits.CompactTitsTraceless.square]

theorem signedEqualCubic_hasSquareLaw : HasSquareLaw signedEqualCubic := by
  intro x
  rw [← gradedTitsEquiv.norm_map (signedEqualCubic.squareMap x), gradedTitsEquiv_signedSquare,
    Tits.CompactTitsTraceless.square_norm_sq, gradedTitsEquiv.norm_map]

/-- The equal-strength signed pencil satisfies the normalized square law. -/
theorem signedPair_hasSquareLaw : HasSquareLaw (interactionCubic signedPair 1) := by
  rw [signedPair_at_one]
  exact signedEqualCubic_hasSquareLaw


end

end ThirteenPlanes
