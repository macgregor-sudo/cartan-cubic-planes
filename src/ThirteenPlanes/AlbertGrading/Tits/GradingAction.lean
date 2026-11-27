module

public import ThirteenPlanes.AlbertGrading.Tits.Automorphisms
public import ThirteenPlanes.AlbertGrading.Tits.HomogeneousProducts
public import ThirteenPlanes.FiniteGroup.Lifts

@[expose] public section

set_option backward.privateInPublic true

/-!
# first-Tits grading and Weyl basis (iii), first half: the character action of `𝔽₃³` on `J_T`

`charLin s` multiplies the Weyl vector `u_q` by `ω^{s·q}`. It is complex linear, commutes with `σ`
and preserves the square, so it restricts to an automorphism `charAut s` of `J_T`. The three
printed generators `Ad_Z`, `Ad_{X⁻¹}`, `φ` are `charLin` of the three unit vectors.
-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem chargeDot_comm' (x y : Charge) : chargeDot x y = chargeDot y x := by
  simp only [chargeDot, mul_comm]

theorem chargeDot_add_left' (x y z : Charge) :
    chargeDot (x + y) z = chargeDot x z + chargeDot y z := by
  simp [chargeDot, add_mul, Finset.sum_add_distrib]

theorem chargeDot_add_right' (x y z : Charge) :
    chargeDot x (y + z) = chargeDot x y + chargeDot x z := by
  simp [chargeDot, mul_add, Finset.sum_add_distrib]

theorem chargeDot_neg_right' (x y : Charge) : chargeDot x (-y) = -chargeDot x y := by
  rw [chargeDot_comm', chargeDot_neg_left, chargeDot_comm']

/-- Multiplication of the 27 graded coordinates by the character `q ↦ ω^{s·q}`. -/
def charAct (s : Charge) : (Charge → ℂ) →ₗ[ℂ] (Charge → ℂ) where
  toFun z q := chargePhase (chargeDot s q) * z q
  map_add' x y := funext fun q => mul_add _ _ _
  map_smul' a z := funext fun q => by
    change _ * (a * z q) = a * (_ * z q)
    exact mul_left_comm _ _ _

@[simp] theorem charAct_apply (s : Charge) (z : Charge → ℂ) (q : Charge) :
    charAct s z q = chargePhase (chargeDot s q) * z q := rfl

theorem charAct_basis (s q : Charge) :
    charAct s (chargeBasisVector q) = chargePhase (chargeDot s q) • chargeBasisVector q := by
  funext i
  simp only [charAct_apply, chargeBasisVector, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h; rfl
  · simp

theorem charAct_gradedProduct (s : Charge) (x y : Charge → ℂ) :
    charAct s (gradedProduct x y) = gradedProduct (charAct s x) (charAct s y) := by
  funext q
  simp only [gradedProduct, charAct_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, chargeBasisVector]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : q = a + b
  · subst h
    simp only [ite_true, mul_one, chargeDot_add_right', chargePhase_add]
    ring
  · simp [h]

private abbrev G := gradedTitsComplexEquiv

/-- The character action on `J_T ⊗ ℂ = FirstTits ℂ`. -/
def charLin (s : Charge) : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ :=
  G.toLinearMap ∘ₗ charAct s ∘ₗ G.symm.toLinearMap

theorem charLin_graded (s : Charge) (z : Charge → ℂ) : charLin s (G z) = G (charAct s z) := by
  change G (charAct s (G.symm (G z))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem charLin_basis (s q : Charge) :
    charLin s (titsBasis q) = chargePhase (chargeDot s q) • titsBasis q := by
  rw [titsBasis_eq_homogeneous, ← gradedTitsCoordinates_single]
  change charLin s (G (chargeBasisVector q)) = _ • G (chargeBasisVector q)
  rw [charLin_graded, charAct_basis, map_smul]

theorem charLin_zero (x : FirstTits ℂ) : charLin 0 x = x := by
  obtain ⟨z, rfl⟩ := G.surjective x
  rw [charLin_graded]
  congr 1
  funext q
  simp [chargeDot]

theorem charLin_add (s t : Charge) (x : FirstTits ℂ) :
    charLin (s + t) x = charLin s (charLin t x) := by
  obtain ⟨z, rfl⟩ := G.surjective x
  rw [charLin_graded, charLin_graded, charLin_graded]
  congr 1
  funext q
  simp only [charAct_apply, chargeDot_add_left', chargePhase_add, mul_assoc]

theorem charLin_involution (s : Charge) (x : FirstTits ℂ) :
    compactInvolution (charLin s x) = charLin s (compactInvolution x) := by
  obtain ⟨z, rfl⟩ := G.surjective x
  change compactInvolution (charLin s (gradedTitsCoordinates z)) =
    charLin s (compactInvolution (gradedTitsCoordinates z))
  rw [compactInvolution_gradedTitsCoordinates]
  change compactInvolution (charLin s (G z)) = charLin s (G _)
  rw [charLin_graded, charLin_graded]
  change compactInvolution (gradedTitsCoordinates _) = gradedTitsCoordinates _
  rw [compactInvolution_gradedTitsCoordinates]
  congr 1
  funext q
  simp only [charAct_apply, star_mul, chargeDot_neg_right', chargePhase_neg, star_star, mul_comm]

theorem charLin_square (s : Charge) (x : FirstTits ℂ) :
    charLin s (firstTitsSquare x) = firstTitsSquare (charLin s x) := by
  obtain ⟨z, rfl⟩ := G.surjective x
  rw [← polar_self, ← polar_self, ← gradedTitsComplexEquiv_product, charLin_graded,
    charLin_graded, charAct_gradedProduct, gradedTitsComplexEquiv_product]

/-- Restriction of the character action to `J_T`. -/
def charAut (s : Charge) : CompactTits ≃ₗ[ℝ] CompactTits :=
  restrictEquiv (charLin s) (charLin (-s)) (charLin_involution s) (charLin_involution (-s))
    (fun x => by rw [← charLin_add, neg_add_cancel, charLin_zero])
    (fun x => by rw [← charLin_add, add_neg_cancel, charLin_zero])

@[simp] theorem charAut_coordinates (s : Charge) (x : CompactTits) :
    CompactTits.coordinates (charAut s x) = charLin s (CompactTits.coordinates x) := rfl

theorem charAut_isAutomorphism (s : Charge) : IsTitsAutomorphism (charAut s) :=
  isTitsAutomorphism_of_coordinates _ (charLin s) (fun _ => rfl) (charLin_square s)

/-- The complex extension of a restricted `σ`-equivariant complex-linear map is that map. -/
theorem complexify_of_coordinates (f : CompactTits →ₗ[ℝ] CompactTits)
    (M : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ)
    (hσ : ∀ x, compactInvolution (M x) = M (compactInvolution x))
    (hf : ∀ x, CompactTits.coordinates (f x) = M (CompactTits.coordinates x)) (z : FirstTits ℂ) :
    complexify f z = M z := by
  rw [complexify, hf, hf]
  change M ((1 / 2 : ℂ) • (z + compactInvolution z)) +
    Complex.I • M ((-Complex.I / 2) • (z - compactInvolution z)) = M z
  simp only [map_smul, map_add, map_sub, smul_add, smul_sub, smul_smul]
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; norm_num
  rw [h]
  module

theorem complexify_charAut (s : Charge) (z : FirstTits ℂ) :
    complexify (charAut s).toLinearMap z = charLin s z :=
  complexify_of_coordinates _ (charLin s) (charLin_involution s) (fun _ => rfl) z

/-! ## The three printed generators -/

private theorem linear_ext_on_basis (M N : FirstTits ℂ →ₗ[ℂ] FirstTits ℂ)
    (h : ∀ q, M (titsBasis q) = N (titsBasis q)) : M = N := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := G.surjective x
  change M (gradedTitsCoordinates z) = N (gradedTitsCoordinates z)
  simp only [gradedTitsCoordinates_sum, map_sum, map_smul, ← titsBasis_eq_homogeneous, h]

private theorem iota_smul (k : ZMod 3) (c : ℂ) (A : Mat3 ℂ) : iota k (c • A) = c • iota k A := by
  simp only [iota]; split_ifs <;> simp

private theorem adMap_iota (U : Mat3 ℂ) (k : ZMod 3) (A : Mat3 ℂ) :
    adMap U (iota k A) = iota k (U * A * Uᴴ) := by
  simp only [adMap, iota]; split_ifs <;> simp

private theorem adMap_basis (U : Mat3 ℂ) (c : ℂ) (k : ZMod 3) (A : Mat3 ℂ)
    (h : U * A * Uᴴ = c • A) : adMap U (iota k A) = c • iota k A := by
  rw [adMap_iota, h, iota_smul]

private theorem clock_mul_apply (A : Matrix (ZMod 3) (ZMod 3) ℂ) (i j : ZMod 3) :
    (clockMatrix * A) i j = chargePhase i * A i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [clockMatrix]
  · intro k _ hk; simp [clockMatrix, Ne.symm hk]
  · simp

private theorem mul_clockT_apply (A : Matrix (ZMod 3) (ZMod 3) ℂ) (i j : ZMod 3) :
    (A * clockMatrixᴴ) i j = A i j * star (chargePhase j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [clockMatrix, Matrix.conjTranspose_apply]
  · intro k _ hk; simp [clockMatrix, Matrix.conjTranspose_apply, Ne.symm hk]
  · simp

private theorem mul_shift_apply (A : Matrix (ZMod 3) (ZMod 3) ℂ) (i j : ZMod 3) :
    (A * shiftMatrix) i j = A i (j + 1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
  · simp [shiftMatrix]
  · intro k _ hk; simp [shiftMatrix, hk]
  · simp

private theorem shiftT_mul_apply (A : Matrix (ZMod 3) (ZMod 3) ℂ) (i j : ZMod 3) :
    (shiftMatrixᴴ * A) i j = A (i + 1) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (i + 1)]
  · simp [shiftMatrix, Matrix.conjTranspose_apply]
  · intro k _ hk; simp [shiftMatrix, Matrix.conjTranspose_apply, hk]
  · simp

private theorem clock_conj (v : WeylLabel) :
    clockMatrix * weylD v * clockMatrixᴴ = chargePhase v.1 • weylD v := by
  rw [weylD_eq_weylMatrix]
  ext i j
  rw [mul_clockT_apply, clock_mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [weylMatrix]
  by_cases h : i = j + v.1
  · subst h
    simp only [ite_true, ← chargePhase_neg, ← chargePhase_add]
    congr 1
    ring
  · simp [h]

theorem shift_conjTranspose_mul : shiftMatrixᴴ * shiftMatrix = 1 := by
  ext i j
  rw [mul_shift_apply]
  simp only [Matrix.conjTranspose_apply, shiftMatrix, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have : ¬ j + 1 = i + 1 := fun e => h (by simpa using e.symm)
    simp [h, this]

theorem shift_inv : shiftMatrix⁻¹ = shiftMatrixᴴ := Matrix.inv_eq_left_inv shift_conjTranspose_mul

private theorem shift_conj (v : WeylLabel) :
    shiftMatrixᴴ * weylD v * shiftMatrixᴴᴴ = chargePhase v.2 • weylD v := by
  rw [Matrix.conjTranspose_conjTranspose, weylD_eq_weylMatrix]
  ext i j
  rw [mul_shift_apply, shiftT_mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [weylMatrix]
  by_cases h : i = j + v.1
  · have h' : i + 1 = j + 1 + v.1 := by rw [h]; ring
    rw [if_pos h', if_pos h, ← chargePhase_add]
    congr 1
    ring
  · have h' : ¬ i + 1 = j + 1 + v.1 := fun e => h (by
      have := congrArg (· - 1) e; simp only [add_sub_cancel_right] at this; rw [this]; ring)
    rw [if_neg h', if_neg h, mul_zero]

theorem adMap_clock_eq : adLin clockMatrix = charLin (Pi.single 0 1) := by
  apply linear_ext_on_basis
  intro q
  rw [charLin_basis, chargeDot_comm', chargeDot_single]
  exact adMap_basis _ _ _ _ (clock_conj (q 0, q 1))

theorem adMap_shiftInv_eq : adLin shiftMatrix⁻¹ = charLin (Pi.single 1 1) := by
  apply linear_ext_on_basis
  intro q
  rw [charLin_basis, chargeDot_comm', chargeDot_single]
  have h := shift_conj (q 0, q 1)
  rw [← shift_inv] at h
  exact adMap_basis _ _ _ _ h

theorem phiMap_eq : phiLin = charLin (Pi.single 2 1) := by
  apply linear_ext_on_basis
  intro q
  rw [charLin_basis, chargeDot_comm', chargeDot_single, phiLin_apply, titsBasis]
  generalize q 2 = k
  generalize weylD (q 0, q 1) = A
  have h10 : (1 : ZMod 3) ≠ 0 := by decide
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have v1 : (1 : ZMod 3).val = 1 := rfl
  have v2 : (2 : ZMod 3).val = 2 := rfl
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) k with rfl | rfl | rfl <;>
    simp [phiMap, iota, chargePhase, h10, h20, h21, h02, h12, h01, v1, v2, Prod.smul_mk] <;>
    exact Prod.ext (by simp) (by simp)

end

end ThirteenPlanes.AlbertGrading
