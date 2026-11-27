module

public import ThirteenPlanes.AlbertGrading.Tits.Product

@[expose] public section

set_option backward.privateInPublic true

/-!
# first-Tits grading and Weyl basis (ii): the 27 vectors `u_g = ι_k(D_v)`

The literal `D_v = ω^{-ab} X^a Z^b` is the `weylMatrix v`, so `u_g` is the accepted
`homogeneousTits g`, whose product table `homogeneousTits_product` is an exact kernel computation
over the cyclotomic integers. Linear dependence over `𝔽₃` is the `dependentGrades`.
-/

open scoped Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

private theorem chargePhase_pow (j : ZMod 3) (n : ℕ) : chargePhase j ^ n = chargePhase (n * j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← chargePhase_add]; congr 1; push_cast; ring

private theorem shiftMatrix_pow (n : ℕ) (i j : ZMod 3) :
    (shiftMatrix ^ n) i j = if i = j + n then 1 else 0 := by
  induction n generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
    · simp only [ih, shiftMatrix, ite_true, mul_one]
      congr 1
      apply propext
      push_cast
      constructor <;> intro h <;> rw [h] <;> ring
    · intro k _ hk
      simp [shiftMatrix, hk]
    · simp

private theorem clockMatrix_pow (n : ℕ) (i j : ZMod 3) :
    (clockMatrix ^ n) i j = if i = j then chargePhase i ^ n else 0 := by
  induction n generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single j]
    · by_cases h : i = j
      · subst h; simp [ih, clockMatrix, pow_succ]
      · simp [ih, clockMatrix, h]
    · intro k _ hk
      simp [clockMatrix, hk]
    · simp

/-- The literal `ω^{-ab} X^a Z^b` is the Weyl matrix. -/
theorem weylD_eq_weylMatrix (v : WeylLabel) : weylD v = weylMatrix v := by
  ext i j
  rw [weylD, Matrix.smul_apply, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [shiftMatrix_pow, clockMatrix_pow, ZMod.natCast_zmod_val, chargePhase_pow,
      ZMod.natCast_zmod_val]
    simp only [ite_true, weylMatrix]
    by_cases h : i = j + v.1
    · simp only [h, ite_true, one_mul, smul_eq_mul, ← chargePhase_add]
      congr 1
      ring
    · simp [h]
  · intro k _ hk
    simp [clockMatrix_pow, hk]
  · simp

theorem titsBasis_eq_homogeneous (g : Charge) : titsBasis g = homogeneousTits g := by
  simp only [titsBasis, iota, homogeneousTits, weylD_eq_weylMatrix]

theorem titsBasis_zero : titsBasis 0 = firstTitsOne := by
  rw [titsBasis_eq_homogeneous, ← gradedTitsCoordinates_single, gradedTitsCoordinates_unit]

theorem titsBasis_involution (g : Charge) :
    compactInvolution (titsBasis g) = titsBasis (-g) := by
  simp only [titsBasis_eq_homogeneous, ← gradedTitsCoordinates_single,
    compactInvolution_gradedTitsCoordinates]
  congr 1
  funext x
  simp only [chargeBasisVector]
  by_cases h : x = -g
  · subst h; simp
  · have h' : -x ≠ g := by intro e; apply h; rw [← e, neg_neg]
    simp [h, h']

theorem titsBasis_traceForm (g h : Charge) :
    titsTraceForm (titsBasis g) (titsBasis h) = if g + h = 0 then 3 else 0 := by
  rw [titsBasis_eq_homogeneous, titsBasis_eq_homogeneous, titsTraceForm_homogeneous]
  rfl

/-- Linear dependence over `𝔽₃` is the four-case `dependentGrades`. -/
theorem f3Dependent_iff (g h : Charge) : F3Dependent g h ↔ dependentGrades g h := by
  constructor
  · rintro ⟨a, b, hab, hsum⟩
    by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := hab.resolve_left (by simp)
      have : b • h = 0 := by simpa using hsum
      right; left
      have := congrArg (fun x => b⁻¹ • x) this
      simpa [smul_smul, inv_mul_cancel₀ hb] using this
    · have hg : g = (-(a⁻¹ * b)) • h := by
        have := congrArg (fun x => a⁻¹ • x) hsum
        simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] at this
        rw [neg_smul, eq_neg_of_add_eq_zero_left this]
      generalize (-(a⁻¹ * b)) = c at hg
      subst hg
      rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 by decide) c with rfl | rfl | rfl
      · left; simp
      · right; right; left; simp
      · right; right; right; simp
  · rintro (h0 | h0 | h0 | h0)
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h0]⟩
    · exact ⟨0, 1, Or.inr one_ne_zero, by simp [h0]⟩
    · exact ⟨1, -1, Or.inl one_ne_zero, by simp [h0]⟩
    · exact ⟨1, 1, Or.inl one_ne_zero, by simp [h0]⟩

theorem titsBasis_product_dependent (g h : Charge) (hd : F3Dependent g h) :
    firstTitsJordanProduct (titsBasis g) (titsBasis h) = titsBasis (g + h) := by
  rw [titsBasis_eq_homogeneous, titsBasis_eq_homogeneous, titsBasis_eq_homogeneous,
    firstTitsJordanProduct_eq_polar, homogeneousTits_product]
  have hd' := (f3Dependent_iff g h).mp hd
  simp [gradedProductCoefficient, hd']

theorem titsBasis_product_independent (v w : WeylLabel) (k l : ZMod 3)
    (hd : ¬ F3Dependent (chargeFrom v k) (chargeFrom w l)) :
    firstTitsJordanProduct (titsBasis (chargeFrom v k)) (titsBasis (chargeFrom w l)) =
      (-(1 / 2 : ℂ) * chargePhase (symplecticBracket v w * (l - k))) •
        titsBasis (chargeFrom v k + chargeFrom w l) := by
  rw [titsBasis_eq_homogeneous, titsBasis_eq_homogeneous, titsBasis_eq_homogeneous,
    firstTitsJordanProduct_eq_polar, homogeneousTits_product]
  rw [f3Dependent_iff] at hd
  congr 1
  simp only [gradedProductCoefficient, hd, ite_false, chargePhase]
  have : gradeExponent (chargeFrom v k) (chargeFrom w l) = symplecticBracket v w * (l - k) := rfl
  rw [this]
  ring

end

end ThirteenPlanes.AlbertGrading
