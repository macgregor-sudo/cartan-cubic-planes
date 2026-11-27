module

public import ThirteenPlanes.SignedTitsCoordinates
public import ThirteenPlanes.SignedPlanes
public import ThirteenPlanes.Tits.Metric

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes

noncomputable section

theorem weylSynthesis_trace_mul (z w : WeylLabel → ℂ) :
    Matrix.trace (weylSynthesis z * weylSynthesis w) = 3 * ∑ v, z v * w (-v) := by
  change Matrix.trace ((∑ v, z v • weylMatrix v) * weylSynthesis w) = _
  rw [Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h := weylSynthesis_coefficient w (-v)
  rw [neg_neg] at h
  rw [Matrix.smul_mul, Matrix.trace_smul, h, smul_eq_mul]
  ring

/-- The complex bilinear trace form in matrix coordinates. -/
def titsTraceForm (x y : FirstTits ℂ) : ℂ :=
  trace3 (x.1 * y.1) + trace3 (x.2.1 * y.2.2) + trace3 (x.2.2 * y.2.1)

private theorem trace3_components_mul (z w : Charge → ℂ) (k l : ZMod 3) :
    trace3 (titsComponent (gradedTitsCoordinates z) k *
      titsComponent (gradedTitsCoordinates w) l) =
      3 * ∑ v, z (chargeFrom v k) * w (chargeFrom (-v) l) := by
  rw [titsComponent_gradedTitsCoordinates, titsComponent_gradedTitsCoordinates]
  calc
    _ = Matrix.trace (weylSynthesis (fun v => z (chargeFrom v k)) *
        weylSynthesis (fun v => w (chargeFrom v l))) := Tits.trace3_eq_matrixTrace _
    _ = _ := weylSynthesis_trace_mul _ _

private theorem sum_zmod_three {A : Type*} [AddCommMonoid A] (f : ZMod 3 → A) :
    ∑ k, f k = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three (show Fin 3 → A from f)

theorem gradedTitsCoordinates_traceForm (z w : Charge → ℂ) :
    titsTraceForm (gradedTitsCoordinates z) (gradedTitsCoordinates w) =
      3 * ∑ x, z x * w (-x) := by
  change trace3 (titsComponent (gradedTitsCoordinates z) 0 *
      titsComponent (gradedTitsCoordinates w) 0) +
      trace3 (titsComponent (gradedTitsCoordinates z) 1 *
      titsComponent (gradedTitsCoordinates w) 2) +
      trace3 (titsComponent (gradedTitsCoordinates z) 2 *
      titsComponent (gradedTitsCoordinates w) 1) = _
  simp only [trace3_components_mul]
  rw [← chargeComponentEquiv.sum_comp (fun x => z x * w (-x))]
  conv_rhs => rw [Fintype.sum_prod_type]
  change _ = 3 * ∑ k : ZMod 3, ∑ v : WeylLabel, z (chargeFrom v k) * w (-chargeFrom v k)
  conv_rhs => rw [sum_zmod_three]
  have hn₁ : -(1 : ZMod 3) = 2 := by decide
  have hn₂ : -(2 : ZMod 3) = 1 := by decide
  simp only [← chargeFrom_neg, neg_zero, hn₁, hn₂]
  ring

/-- Extend real signed fields to the trace-free complex charge coordinates. -/
def signedExtend : SignedField →ₗ[ℝ] (Charge → ℂ) where
  toFun z x := if h : x = 0 then 0 else signedCoordinates z ⟨x, h⟩
  map_add' x y := by
    funext q
    by_cases h : q = 0 <;> simp [h]
  map_smul' r x := by
    funext q
    by_cases h : q = 0 <;> simp [h]

@[simp] theorem signedExtend_zero (x : SignedField) : signedExtend x 0 = 0 := by
  simp [signedExtend]

@[simp] theorem signedExtend_nonzero (x : SignedField) (q : NonzeroCharge) :
    signedExtend x q.val = signedCoordinates x q := by
  simp [signedExtend, q.property]

theorem signedExtend_neg (x : SignedField) (q : Charge) :
    signedExtend x (-q) = star (signedExtend x q) := by
  by_cases h : q = 0
  · subst q
    simp
  · let p : NonzeroCharge := ⟨q,h⟩
    change signedExtend x (oppositeCharge p).val = star (signedExtend x p.val)
    rw [signedExtend_nonzero, signedExtend_nonzero, signedCoordinates_opposite]

private def realCoordinates : (Charge → ℂ) →ₗ[ℝ] FirstTits ℂ :=
  gradedTitsCoordinates.restrictScalars ℝ

private theorem signedCoordinates_fixed (x : SignedField) :
    Tits.compactInvolution (realCoordinates (signedExtend x)) = realCoordinates (signedExtend x) := by
  change Tits.compactInvolution (gradedTitsCoordinates (signedExtend x)) =
    gradedTitsCoordinates (signedExtend x)
  rw [compactInvolution_gradedTitsCoordinates]
  congr 1
  funext q
  rw [signedExtend_neg, star_star]

private def signedToTits (x : SignedField) : Tits.CompactTitsTraceless :=
  ⟨Tits.CompactTits.ofFixed (realCoordinates (signedExtend x)) (signedCoordinates_fixed x), by
    change Tits.CompactTits.trace
      (Tits.CompactTits.ofFixed (realCoordinates (signedExtend x)) (signedCoordinates_fixed x)) = 0
    rw [Tits.CompactTits.trace_apply, Tits.CompactTits.coordinates_ofFixed]
    change (trace3 (gradedTitsCoordinates (signedExtend x)).1).re = 0
    simp [gradedTitsCoordinates_trace]⟩

@[simp] theorem signedToTits_coordinates (x : SignedField) :
    Tits.CompactTitsTraceless.coordinates (signedToTits x) =
      gradedTitsCoordinates (signedExtend x) := rfl

private theorem compactTracelessCoordinates_injective :
    Function.Injective Tits.CompactTitsTraceless.coordinates :=
  fun _ _ h => Subtype.ext (Tits.CompactTits.ext h)

private def signedToTitsLinear : SignedField →ₗ[ℝ] Tits.CompactTitsTraceless where
  toFun := signedToTits
  map_add' x y := compactTracelessCoordinates_injective (by
    simp only [signedToTits_coordinates, map_add])
  map_smul' r x := compactTracelessCoordinates_injective (by
    simp only [signedToTits_coordinates, map_smul]
    exact (realCoordinates.map_smul r (signedExtend x)))

private theorem signedToTitsLinear_injective : Function.Injective signedToTitsLinear := by
  intro x y h
  have hz := congrArg Tits.CompactTitsTraceless.coordinates h
  change gradedTitsCoordinates (signedExtend x) = gradedTitsCoordinates (signedExtend y) at hz
  have he := gradedTitsComplexEquiv.injective hz
  apply signedFields.subtype_injective
  funext q
  change signedCoordinates x q = signedCoordinates y q
  simpa only [signedExtend_nonzero] using congrFun he q.val

private theorem signedToTitsLinear_surjective : Function.Surjective signedToTitsLinear := by
  intro y
  let z : Charge → ℂ := gradedTitsComplexEquiv.symm (Tits.CompactTitsTraceless.coordinates y)
  have hz : gradedTitsCoordinates z = Tits.CompactTitsTraceless.coordinates y :=
    gradedTitsComplexEquiv.apply_symm_apply _
  have hf := Tits.CompactTits.fixed y.val
  change Tits.compactInvolution (Tits.CompactTitsTraceless.coordinates y) =
    Tits.CompactTitsTraceless.coordinates y at hf
  rw [← hz, compactInvolution_gradedTitsCoordinates] at hf
  have hf' := gradedTitsComplexEquiv.injective hf
  have hconj (q : Charge) : z (-q) = star (z q) := by
    simpa only [neg_neg] using (congrFun hf' (-q)).symm
  have ht := Tits.CompactTitsTraceless.complex_trace_zero y
  rw [← hz, gradedTitsCoordinates_trace] at ht
  have hzero : z 0 = 0 := by linear_combination ht / 3
  let x : SignedField := ⟨fun q => z q.val, fun q => hconj q.val⟩
  refine ⟨x, compactTracelessCoordinates_injective ?_⟩
  change gradedTitsCoordinates (signedExtend x) = Tits.CompactTitsTraceless.coordinates y
  rw [← hz]
  congr 1
  funext q
  by_cases he : q = 0
  · subst q
    simp [hzero]
  · exact signedExtend_nonzero x (⟨q,he⟩ : NonzeroCharge)

private theorem signedExtend_norm_sum (x : SignedField) :
    ∑ q : Charge, ‖signedExtend x q‖ ^ 2 = ∑ q : NonzeroCharge, ‖signedCoordinates x q‖ ^ 2 := by
  classical
  have h : ∑ q : NonzeroCharge, ‖signedCoordinates x q‖ ^ 2 =
      ∑ q ∈ (Finset.univ : Finset Charge) with q ≠ 0, ‖signedExtend x q‖ ^ 2 := by
    simpa only [Finset.subtype_univ, signedExtend_nonzero] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset Charge))
        (f := fun q => ‖signedExtend x q‖ ^ 2) (p := fun q => q ≠ 0))
  rw [h]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q _ hn
  have hq : q = 0 := by simpa using hn
  subst q
  simp

private theorem signedToTits_norm (x : SignedField) : ‖signedToTits x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(signedToTits x).val‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, Tits.CompactTits.inner_eq_complexTrace_re]
  change (titsTraceForm (gradedTitsCoordinates (signedExtend x))
    (gradedTitsCoordinates (signedExtend x))).re = _
  rw [gradedTitsCoordinates_traceForm, signedField_norm_sq, Complex.mul_re]
  simp only [show (3 : ℂ).re = 3 from Complex.natCast_re 3,
    show (3 : ℂ).im = 0 from Complex.natCast_im 3, zero_mul, sub_zero, Complex.re_sum,
    signedExtend_neg, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re, signedExtend_norm_sum]

/-- The signed real field space and the traceless compact Tits form are linearly isometric. -/
def gradedTitsEquiv : SignedField ≃ₗᵢ[ℝ] Tits.CompactTitsTraceless where
  toLinearEquiv := LinearEquiv.ofBijective signedToTitsLinear
    ⟨signedToTitsLinear_injective, signedToTitsLinear_surjective⟩
  norm_map' := signedToTits_norm

@[simp] theorem gradedTitsEquiv_coordinates (x : SignedField) :
    Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv x) =
      gradedTitsCoordinates (signedExtend x) := rfl

end

end ThirteenPlanes
