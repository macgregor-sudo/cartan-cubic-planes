module

public import ThirteenPlanes.AlbertGrading.Cubic.Coordinates
public import ThirteenPlanes.AlbertGrading.Cubic.Statements
public import ThirteenPlanes.AlbertGrading.Tits.Main
public import ThirteenPlanes.AlbertGrading.Contrast.Bridge

@[expose] public section

/-! Explicit phase exponents in the compact first Tits model.

The product table and trace form of the Tits basis determine the coefficients `T(u_g∘u_h,u_k)`.
Their expansion over zero-sum triples gives the normalized cubic with exponent
`φ_{ghk} = [v,w](l-k')` for `g = (v,k')` and `h = (w,l)`. -/

open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

open Grading Tits

noncomputable section

namespace Cubic

/-! ## Bilinearity -/

theorem trace3_add' (A B : Mat3 ℂ) : trace3 (A + B) = trace3 A + trace3 B := by
  simp only [trace3, Matrix.add_apply]; ring

theorem trace3_smul' (c : ℂ) (A : Mat3 ℂ) : trace3 (c • A) = c * trace3 A := by
  simp only [trace3, Matrix.smul_apply, smul_eq_mul]; ring

theorem tf_add_left (x y z : FirstTits ℂ) :
    titsTraceForm (x + y) z = titsTraceForm x z + titsTraceForm y z := by
  simp only [titsTraceForm, Prod.fst_add, Prod.snd_add, Matrix.add_mul, trace3_add']; ring

theorem tf_add_right (x y z : FirstTits ℂ) :
    titsTraceForm x (y + z) = titsTraceForm x y + titsTraceForm x z := by
  simp only [titsTraceForm, Prod.fst_add, Prod.snd_add, Matrix.mul_add, trace3_add']; ring

theorem tf_smul_left (c : ℂ) (x z : FirstTits ℂ) :
    titsTraceForm (c • x) z = c * titsTraceForm x z := by
  simp only [titsTraceForm, Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, trace3_smul']; ring

theorem tf_smul_right (c : ℂ) (x z : FirstTits ℂ) :
    titsTraceForm x (c • z) = c * titsTraceForm x z := by
  simp only [titsTraceForm, Prod.smul_fst, Prod.smul_snd, Matrix.mul_smul, trace3_smul']; ring

/-- `T` as a bilinear map. -/
def tfBil : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ titsTraceForm tf_add_left tf_smul_left tf_add_right tf_smul_right

/-- The printed product as a bilinear map. -/
def ppBil : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ →ₗ[ℂ] FirstTits ℂ :=
  LinearMap.mk₂ ℂ firstTitsJordanProduct
    (fun x y z => by simp only [firstTitsJordanProduct_eq_polar]; exact Contrast.tProd_add_left x y z)
    (fun c x y => by simp only [firstTitsJordanProduct_eq_polar]; exact Contrast.tProd_smul_left c x y)
    (fun x y z => by simp only [firstTitsJordanProduct_eq_polar]; exact Contrast.tProd_add_right x y z)
    (fun c x y => by simp only [firstTitsJordanProduct_eq_polar]; exact Contrast.tProd_smul_right c x y)

theorem tf_pp_sum (c : ℂ) (Z : NonzeroCharge → ℂ) (U : NonzeroCharge → FirstTits ℂ) :
    titsTraceForm (firstTitsJordanProduct (c • ∑ k, Z k • U k) (c • ∑ k, Z k • U k)) (c • ∑ k, Z k • U k) =
      c ^ 3 * ∑ x : Triple, titsTraceForm (firstTitsJordanProduct (U x.1) (U x.2.1)) (U x.2.2) *
        Z x.1 * Z x.2.1 * Z x.2.2 := by
  have e1 : ∀ x y, firstTitsJordanProduct x y = ppBil x y := fun _ _ => rfl
  have e2 : ∀ x y, titsTraceForm x y = tfBil x y := fun _ _ => rfl
  simp only [e1, e2, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

/-! ## The coefficients of the Tits basis -/

/-- `T(u_a ∘ u_b, u_c)` for the Tits basis. -/
def titsCoeff : Coeff := fun a b c =>
  titsTraceForm (firstTitsJordanProduct (titsBasis a.val) (titsBasis b.val)) (titsBasis c.val)

theorem chargeFrom_eta (g : Charge) : chargeFrom (g 0, g 1) (g 2) = g := by
  funext i; fin_cases i <;> rfl

theorem three_zero (k : Charge) : k + k + k = 0 := by
  rw [charge_add_self]; abel

theorem titsCoeff_formula (a b c : NonzeroCharge) :
    titsCoeff a b c = if a.val + b.val + c.val = 0 then
      (if a = b then 3 else -(3 / 2 : ℂ) * chargePhase (titsPhase (a, b, c))) else 0 := by
  unfold titsCoeff
  by_cases hab : a = b
  · subst hab
    rw [titsBasis_product_dependent _ _ ⟨1, -1, Or.inl one_ne_zero, by simp⟩, titsBasis_traceForm]
    simp
  · by_cases hneg : b.val = -a.val
    · rw [titsBasis_product_dependent _ _ ⟨1, 1, Or.inl one_ne_zero, by simp [hneg]⟩,
        titsBasis_traceForm]
      have h0 : a.val + b.val = 0 := by rw [hneg]; abel
      rw [h0, zero_add]
      simp [c.property]
    · have hind : ¬ F3Dependent (chargeFrom (a.val 0, a.val 1) (a.val 2))
          (chargeFrom (b.val 0, b.val 1) (b.val 2)) := by
        rw [chargeFrom_eta, chargeFrom_eta, f3Dependent_iff]
        rintro (h | h | h | h)
        · exact a.property h
        · exact b.property h
        · exact hab (Subtype.ext h)
        · exact hneg (by rw [h, neg_neg])
      have hp := titsBasis_product_independent _ _ _ _ hind
      rw [chargeFrom_eta, chargeFrom_eta] at hp
      rw [hp, tf_smul_left, titsBasis_traceForm, if_neg hab]
      unfold titsPhase
      split_ifs <;> ring

section Data

variable (sgn : SignedPlaneIndex → Bool) (ζ : SignedPlaneIndex → ℂ)

theorem titsPhase_swap12 (a b c : NonzeroCharge) : titsPhase (b, a, c) = titsPhase (a, b, c) := by
  simp only [titsPhase, symplecticBracket]; ring

theorem titsPhase_neg (a b c : NonzeroCharge) :
    titsPhase (oppositeCharge a, oppositeCharge b, oppositeCharge c) = -titsPhase (a, b, c) := by
  simp only [titsPhase, symplecticBracket, opp_val, Pi.neg_apply]; ring

theorem titsPhase_swap23 {a b c : NonzeroCharge} (hs : a.val + b.val + c.val = 0) :
    titsPhase (a, c, b) = titsPhase (a, b, c) := by
  have hc : ∀ i, c.val i = -(a.val i + b.val i) := fun i => by
    have := congrFun hs i; simp only [Pi.add_apply, Pi.zero_apply] at this
    linear_combination this
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp only [titsPhase, symplecticBracket, hc]
  linear_combination (a.val 0 * b.val 1 - a.val 1 * b.val 0) * a.val 2 * h3

theorem titsCoeff_data : CubicData titsCoeff (gradeCoord sgn ζ) where
  zero a b c h := by rw [titsCoeff_formula, if_neg h]
  swap12 a b c := by
    rw [titsCoeff_formula, titsCoeff_formula, titsPhase_swap12, show b.val + a.val + c.val =
      a.val + b.val + c.val by abel]
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  swap23 a b c := by
    rw [titsCoeff_formula, titsCoeff_formula, show a.val + c.val + b.val =
      a.val + b.val + c.val by abel]
    by_cases hs : a.val + b.val + c.val = 0
    · rw [if_pos hs, if_pos hs, titsPhase_swap23 hs]
      have hiff : a = b ↔ a = c := by
        constructor
        · rintro rfl; apply Subtype.ext
          have : c.val = -(a.val + a.val) := by linear_combination hs
          rw [this, charge_add_self, neg_neg]
        · rintro rfl; apply Subtype.ext
          have : b.val = -(a.val + a.val) := by linear_combination hs
          rw [this, charge_add_self, neg_neg]
      by_cases h : a = b
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun e => h (hiff.mpr e))]
    · rw [if_neg hs, if_neg hs]
  neg a b c := by
    rw [titsCoeff_formula, titsCoeff_formula, titsPhase_neg, chargePhase_neg]
    have hc : (oppositeCharge a).val + (oppositeCharge b).val + (oppositeCharge c).val = 0 ↔
        a.val + b.val + c.val = 0 := by
      simp only [opp_val]; rw [← neg_add, ← neg_add, neg_eq_zero]
    by_cases hs : a.val + b.val + c.val = 0
    · rw [if_pos (hc.mpr hs), if_pos hs]
      by_cases h : a = b
      · rw [if_pos h, if_pos (opp_inj.mpr h)]; simp
      · rw [if_neg h, if_neg (fun e => h (opp_inj.mp e)), star_mul']; simp
    · rw [if_neg (fun e => hs (hc.mp e)), if_neg hs, star_zero]
  diag k := by rw [titsCoeff_formula, if_pos (three_zero k.val), if_pos rfl]
  coord k := gradeCoord_opp sgn ζ k

theorem titsTerm_eq_tT {x : Triple} (hs : x.1.val + x.2.1.val + x.2.2.val = 0) (hne : x.1 ≠ x.2.1) :
    titsTerm sgn ζ x = tT titsCoeff (gradeCoord sgn ζ) x := by
  unfold titsTerm tT
  rw [titsCoeff_formula, if_pos hs, if_neg hne]
  congr 1; ring

theorem titsValue_eq_tV {t : Finset SignedPlaneIndex} (ht : t ∈ signedCollinearTriples) :
    titsValue sgn ζ t = tV titsCoeff (gradeCoord sgn ζ) t := by
  unfold titsValue tV
  split_ifs with h
  · have hm := mem_repsF.mpr h.some_mem
    obtain ⟨p1, -, -⟩ := proper_of_mem_reps ht hm
    rw [repsF, Finset.mem_filter] at hm
    exact titsTerm_eq_tT sgn ζ hm.2.1 (ne_of_point_ne p1)
  · rfl

theorem sum_field_tits :
    ∑ p, (ζ p • titsBasis (signedGrade p (sgn p)).val +
        star (ζ p) • titsBasis (-(signedGrade p (sgn p)).val)) =
      ∑ k, gradeCoord sgn ζ k • titsBasis k.val := by
  rw [sum_nonzero]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [gradeCoord_signedGrade, gradeCoord_signedGrade]
  have ht : (signedGrade p true).val = -(signedGrade p false).val := rfl
  have hf : (signedGrade p false).val = -(signedGrade p true).val := by rw [ht, neg_neg]
  cases h : sgn p
  · simp only [ht, ite_true, Bool.true_eq_false, ite_false]
  · simp only [hf, ite_true, Bool.false_eq_true, ite_false]; rw [add_comm]

end Data

end Cubic

end

end ThirteenPlanes.AlbertGrading
