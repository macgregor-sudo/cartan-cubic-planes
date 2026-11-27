module

public import ThirteenPlanes.AlbertGrading.Recognition.Statements

@[expose] public section

set_option backward.privateInPublic true

/-!
# Contrast algebra in `J_T ⊗ ℂ`

The basis `u_g` gives coefficient functionals for the bilinear first-Tits product.
The frame relations give the contrast identities in `J_T`. A contrast on the line `ℂ u_k`
then identifies the frame with the graded frame of `{±k}`.

-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-! ## The product is complex bilinear -/

private theorem trace3_add' (a b : Mat3 ℂ) : trace3 (a + b) = trace3 a + trace3 b := by
  simp only [trace3, Matrix.add_apply]; ring

private theorem trace3_smul' (c : ℂ) (a : Mat3 ℂ) : trace3 (c • a) = c * trace3 a := by
  simp only [trace3, Matrix.smul_apply, smul_eq_mul]; ring

private theorem trace3_mul_comm' (a b : Mat3 ℂ) : trace3 (a * b) = trace3 (b * a) := by
  rw [trace3_eq_matrixTrace, trace3_eq_matrixTrace, Matrix.trace_mul_comm]

theorem firstTitsJordanProduct_comm (x y : FirstTits ℂ) : firstTitsJordanProduct x y = firstTitsJordanProduct y x := by
  obtain ⟨A, B, C⟩ := x
  obtain ⟨P, Q, R⟩ := y
  simp only [firstTitsJordanProduct, sharpPair]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [add_comm (A * P), add_comm (B * R)]
  · simp only [trace3_mul_comm' C R]; module
  · simp only [trace3_mul_comm' B Q]; module

theorem firstTitsJordanProduct_add_left (x x' y : FirstTits ℂ) :
    firstTitsJordanProduct (x + x') y = firstTitsJordanProduct x y + firstTitsJordanProduct x' y := by
  obtain ⟨A, B, C⟩ := x
  obtain ⟨A', B', C'⟩ := x'
  obtain ⟨P, Q, R⟩ := y
  simp only [firstTitsJordanProduct, sharpPair, Prod.mk_add_mk, Matrix.add_mul, Matrix.mul_add, trace3_add',
    add_mul, mul_add, add_smul, smul_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> module

theorem firstTitsJordanProduct_smul_left (c : ℂ) (x y : FirstTits ℂ) :
    firstTitsJordanProduct (c • x) y = c • firstTitsJordanProduct x y := by
  obtain ⟨A, B, C⟩ := x
  obtain ⟨P, Q, R⟩ := y
  simp only [firstTitsJordanProduct, sharpPair, Prod.smul_mk, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
    trace3_smul']
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> module

/-- The product `(5-tits)` as a complex bilinear map. -/
def firstTitsJordanBilinear : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ →ₗ[ℂ] FirstTits ℂ :=
  LinearMap.mk₂ ℂ firstTitsJordanProduct firstTitsJordanProduct_add_left firstTitsJordanProduct_smul_left
    (fun x y y' => by
      rw [firstTitsJordanProduct_comm, firstTitsJordanProduct_add_left, firstTitsJordanProduct_comm, firstTitsJordanProduct_comm y' x])
    (fun c x y => by rw [firstTitsJordanProduct_comm, firstTitsJordanProduct_smul_left, firstTitsJordanProduct_comm])

@[simp] theorem firstTitsJordanBilinear_apply (x y : FirstTits ℂ) : firstTitsJordanBilinear x y = firstTitsJordanProduct x y := rfl

theorem firstTitsJordanProduct_smul_smul (a b : ℂ) (x y : FirstTits ℂ) :
    firstTitsJordanProduct (a • x) (b • y) = (a * b) • firstTitsJordanProduct x y := by
  rw [firstTitsJordanProduct_smul_left, firstTitsJordanProduct_comm x, firstTitsJordanProduct_smul_left, firstTitsJordanProduct_comm y,
    smul_smul]

/-! ## Coefficients in the basis `u_g`, and the trace -/

/-- The coefficient of `u_g`. -/
def coef (g : Charge) : FirstTits ℂ →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp gradedTitsComplexEquiv.symm.toLinearMap

theorem titsBasis_eq_equiv (h : Charge) :
    titsBasis h = gradedTitsComplexEquiv (chargeBasisVector h) := by
  rw [titsBasis_eq_homogeneous, gradedTitsComplexEquiv_apply, gradedTitsCoordinates_single]

@[simp] theorem coef_titsBasis (g h : Charge) :
    coef g (titsBasis h) = if g = h then 1 else 0 := by
  rw [coef, LinearMap.comp_apply, LinearEquiv.coe_coe, titsBasis_eq_equiv,
    LinearEquiv.symm_apply_apply]
  simp [chargeBasisVector, eq_comm]

theorem coef_one (g : Charge) : coef g firstTitsOne = if g = 0 then 1 else 0 := by
  rw [← titsBasis_zero, coef_titsBasis]

theorem titsBasis_ne_zero' (g : Charge) : titsBasis g ≠ 0 := by
  intro h
  have := coef_titsBasis g g
  simp [h] at this

theorem firstTitsOne_ne_zero : (firstTitsOne : FirstTits ℂ) ≠ 0 := by
  rw [← titsBasis_zero]; exact titsBasis_ne_zero' 0

/-- The trace of the first matrix coordinate, complex-linearly. -/
def tr1 : FirstTits ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin 3) ℂ ℂ).comp (LinearMap.fst ℂ (Mat3 ℂ) (Mat3 ℂ × Mat3 ℂ))

theorem tr1_apply (x : FirstTits ℂ) : tr1 x = trace3 x.1 := by
  simp [tr1, trace3_eq_matrixTrace]

theorem tr1_titsBasis (g : Charge) : tr1 (titsBasis g) = if g = 0 then 3 else 0 := by
  have h := titsBasis_traceForm 0 g
  rw [titsBasis_zero] at h
  simp only [titsTraceForm, firstTitsOne, Matrix.one_mul, Matrix.zero_mul, zero_add] at h
  rw [tr1_apply]
  have h0 : trace3 (0 : Mat3 ℂ) = 0 := by simp [trace3]
  rw [h0, add_zero, add_zero] at h
  rw [h]

theorem tr1_one : tr1 firstTitsOne = 3 := by
  rw [← titsBasis_zero, tr1_titsBasis]; simp

/-! ## Elementary facts on `ω` and charges -/

theorem chargePhase_ne_zero' (a : ZMod 3) : chargePhase a ≠ 0 :=
  pow_ne_zero _ chargeRoot_ne_zero

theorem chargePhase_one' : chargePhase 1 = chargeRoot := pow_one _

theorem chargePhase_two' : chargePhase 2 = chargeRoot ^ 2 := rfl

theorem chargePhase_sub (a b : ZMod 3) :
    chargePhase (a - b) = chargePhase a * chargePhase (-b) := by
  rw [sub_eq_add_neg, chargePhase_add]

theorem chargePhase_mul_neg' (a : ZMod 3) : chargePhase a * chargePhase (-a) = 1 := by
  rw [← chargePhase_add, add_neg_cancel, chargePhase_zero]

/-- `1 + ω^t + ω^{-t}` is `3` at `t = 0` and `0` otherwise. -/
theorem chargePhase_triple (t : ZMod 3) :
    1 + chargePhase t + chargePhase (-t) = if t = 0 then 3 else 0 := by
  have hq := chargeRoot_quadratic
  rcases (show ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2 by decide) t with rfl | rfl | rfl
  · rw [if_pos rfl, neg_zero, chargePhase_zero]; norm_num
  · rw [show chargePhase (-(1 : ZMod 3)) = chargeRoot ^ 2 from rfl, if_neg (by decide),
      chargePhase_one']
    linear_combination hq
  · rw [show chargePhase (-(2 : ZMod 3)) = chargeRoot from pow_one _, if_neg (by decide),
      chargePhase_two']
    linear_combination hq

theorem chargePhase_sum : ∑ a : ZMod 3, chargePhase a = 0 := by
  rw [sum_zmod3, chargePhase_zero, chargePhase_one', chargePhase_two']
  linear_combination chargeRoot_quadratic

theorem cube_root (l : ℂ) (h : l ^ 3 = 1) : ∃ j : ZMod 3, l = chargePhase j := by
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  have hE : (l - 1) * ((l - chargeRoot) * (l - chargeRoot ^ 2)) = 0 := by
    linear_combination h + (-l ^ 2 + chargeRoot * l) * hq - hc
  rcases mul_eq_zero.mp hE with h1 | h2
  · exact ⟨0, by rw [chargePhase_zero]; linear_combination h1⟩
  rcases mul_eq_zero.mp h2 with h3 | h4
  · exact ⟨1, by rw [chargePhase_one']; linear_combination h3⟩
  · exact ⟨2, by rw [chargePhase_two']; linear_combination h4⟩

theorem charge_add_self (k : Charge) : k + k = -k := by
  funext i
  have : ∀ x : ZMod 3, x + x = -x := by decide
  exact this (k i)

theorem dep_self (k : Charge) : F3Dependent k k :=
  ⟨1, -1, Or.inl one_ne_zero, by simp⟩

theorem dep_neg (k : Charge) : F3Dependent k (-k) :=
  ⟨1, 1, Or.inl one_ne_zero, by simp⟩

theorem dep_neg' (k : Charge) : F3Dependent (-k) k :=
  ⟨1, 1, Or.inl one_ne_zero, by simp⟩

theorem dep_neg_neg (k : Charge) : F3Dependent (-k) (-k) :=
  ⟨1, -1, Or.inl one_ne_zero, by simp⟩

theorem titsBasis_indep (g h : Charge) (hd : ¬ F3Dependent g h) :
    ∃ c : ℂ, c ≠ 0 ∧ firstTitsJordanProduct (titsBasis g) (titsBasis h) = c • titsBasis (g + h) := by
  have hg := chargeFrom_components g
  have hh := chargeFrom_components h
  rw [← hg, ← hh] at hd ⊢
  exact ⟨_, mul_ne_zero (by norm_num) (chargePhase_ne_zero' _),
    titsBasis_product_independent _ _ _ _ hd⟩

/-! ## Contrasts of frames of `J_T` -/

section Frame

variable {P : ZMod 3 → CompactTits}

local notation "X" => fun a => CompactTits.coordinates (P a)

theorem frame_coordinates_product (hP : IsTitsFrame P) (a b : ZMod 3) :
    firstTitsJordanProduct (CompactTits.coordinates (P a)) (CompactTits.coordinates (P b)) =
      if a = b then CompactTits.coordinates (P a) else 0 := by
  rw [← coordinates_product, hP.1 a b]
  split <;> simp

theorem frame_product_sum (hP : IsTitsFrame P) (c d : ZMod 3 → ℂ) :
    firstTitsJordanProduct (∑ a, c a • CompactTits.coordinates (P a))
        (∑ b, d b • CompactTits.coordinates (P b)) =
      ∑ a, (c a * d a) • CompactTits.coordinates (P a) := by
  simp only [sum_zmod3, ← firstTitsJordanBilinear_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply]
  simp only [firstTitsJordanBilinear_apply, frame_coordinates_product hP]
  simp only [show (0 : ZMod 3) ≠ 1 by decide, show (0 : ZMod 3) ≠ 2 by decide,
    show (1 : ZMod 3) ≠ 0 by decide, show (1 : ZMod 3) ≠ 2 by decide,
    show (2 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 1 by decide, if_true, if_false,
    smul_zero, add_zero, zero_add]
  module

theorem frame_sum (hP : IsTitsFrame P) :
    ∑ a, CompactTits.coordinates (P a) = firstTitsOne := by
  rw [← map_sum, hP.2.2, CompactTits.coordinates_one]

theorem involution_contrast (P : ZMod 3 → CompactTits) :
    compactInvolution (titsContrast P) = ∑ a, chargePhase (-a) • CompactTits.coordinates (P a) := by
  simp only [titsContrast, map_sum, compactInvolution_complex_smul, CompactTits.fixed,
    ← chargePhase_neg]

theorem contrast_square (hP : IsTitsFrame P) :
    firstTitsJordanProduct (titsContrast P) (titsContrast P) = compactInvolution (titsContrast P) := by
  rw [involution_contrast, titsContrast, frame_product_sum hP]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← chargePhase_add]
  congr 2
  have : ∀ x : ZMod 3, x + x = -x := by decide
  exact this a

theorem contrast_mul_involution (hP : IsTitsFrame P) :
    firstTitsJordanProduct (titsContrast P) (compactInvolution (titsContrast P)) = firstTitsOne := by
  rw [involution_contrast, titsContrast, frame_product_sum hP, ← frame_sum hP]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chargePhase_mul_neg', one_smul]

theorem contrast_trace (hP : IsTitsFrame P) : tr1 (titsContrast P) = 0 := by
  have ht (a : ZMod 3) : tr1 (CompactTits.coordinates (P a)) = 1 := by
    rw [tr1_apply, ← CompactTits.complex_trace_eq, hP.2.1 a, Complex.ofReal_one]
  simp only [titsContrast, map_sum, map_smul, ht, smul_eq_mul, mul_one]
  exact chargePhase_sum

/-- Fourier inversion: `p_a = (e + ω^{-a} u + ω^a σu)/3`. -/
theorem frame_fourier (hP : IsTitsFrame P) (a : ZMod 3) :
    CompactTits.coordinates (P a) =
      (1 / 3 : ℂ) • (firstTitsOne + chargePhase (-a) • titsContrast P +
        chargePhase a • compactInvolution (titsContrast P)) := by
  rw [involution_contrast, titsContrast, ← frame_sum hP, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.smul_sum]
  simp only [smul_smul, ← add_smul]
  rw [Finset.sum_eq_single a]
  · rw [← chargePhase_add, ← chargePhase_add, neg_add_cancel, add_neg_cancel, chargePhase_zero]
    module
  · intro b _ hb
    have h := chargePhase_triple (b - a)
    rw [if_neg (sub_ne_zero.mpr hb), chargePhase_sub, neg_sub, chargePhase_sub, mul_comm] at h
    have e : ∀ (c1 c2 : ℂ) (x : FirstTits ℂ),
        (1 / 3 : ℂ) • (x + c1 • x + c2 • x) = ((1 / 3) * (1 + c1 + c2)) • x := by
      intros; module
    rw [e, show (1 : ℂ) + chargePhase (-a) * chargePhase b + chargePhase a * chargePhase (-b) = 0 by
      linear_combination h, mul_zero, zero_smul]
  · simp

theorem contrast_ne_zero (hP : IsTitsFrame P) : titsContrast P ≠ 0 := by
  intro h
  have := contrast_mul_involution hP
  rw [h, ← firstTitsJordanBilinear_apply, map_zero, LinearMap.zero_apply] at this
  exact firstTitsOne_ne_zero this.symm

/-- The last step of the proof of the recognition of the graded frame system: a contrast on the line `ℂ u_k`, `k ≠ 0`,
is `ω^j u_k`, and Fourier inversion gives `p_a = p_{k,a-j}`. -/
theorem frame_of_line (hP : IsTitsFrame P) {k : Charge} {l : ℂ}
    (hu : titsContrast P = l • titsBasis k) :
    ∃ j : ZMod 3, ∀ a, P a = gradedFrame k (a - j) := by
  have h1 := contrast_square hP
  have h2 := contrast_mul_involution hP
  have hs : compactInvolution (titsContrast P) = star l • titsBasis (-k) := by
    rw [hu, compactInvolution_complex_smul, titsBasis_involution]
  rw [hs, hu, firstTitsJordanProduct_smul_smul, titsBasis_product_dependent _ _ (dep_self k),
    charge_add_self] at h1
  rw [hs, hu, firstTitsJordanProduct_smul_smul, titsBasis_product_dependent _ _ (dep_neg k), add_neg_cancel,
    titsBasis_zero] at h2
  have hl2 : l * l = star l := smul_left_injective ℂ (titsBasis_ne_zero' _) h1
  have hl1 : l * star l = 1 := by
    have := congrArg (coef 0) h2
    rw [map_smul, coef_one, if_pos rfl, smul_eq_mul, mul_one] at this
    exact this
  obtain ⟨j, rfl⟩ := cube_root l (by
    have e : l ^ 3 = l * (l * l) := by ring
    rw [e, hl2, hl1])
  refine ⟨j, fun a => CompactTits.ext ?_⟩
  rw [frame_fourier hP, hs, hu, gradedFrame_coordinates, gradedCoords, smul_smul, smul_smul,
    ← chargePhase_neg, ← chargePhase_add, ← chargePhase_add, neg_sub, sub_eq_add_neg a j]
  congr 3
  ring

theorem range_eq_of_line (hP : IsTitsFrame P) {k : Charge} {l : ℂ}
    (hu : titsContrast P = l • titsBasis k) : Set.range P = Set.range (gradedFrame k) := by
  obtain ⟨j, hj⟩ := frame_of_line hP hu
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a - j, (hj a).symm⟩
  · rintro ⟨b, rfl⟩; exact ⟨b + j, by rw [hj]; congr 1; ring⟩

end Frame

/-- The two graded frames of `g` and `-g` are the same set. -/
theorem gradedFrame_neg (g : Charge) (a : ZMod 3) : gradedFrame (-g) a = gradedFrame g (-a) := by
  apply CompactTits.ext
  simp only [gradedFrame_coordinates, gradedCoords, neg_neg]
  congr 1
  abel

theorem range_gradedFrame_neg (g : Charge) :
    Set.range (gradedFrame (-g)) = Set.range (gradedFrame g) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨-a, (gradedFrame_neg g a).symm⟩
  · rintro ⟨a, rfl⟩; exact ⟨-a, by rw [gradedFrame_neg, neg_neg]⟩

end

end ThirteenPlanes.AlbertGrading
