module

public import ThirteenPlanes.SignedTitsUnital
public import ThirteenPlanes.NativeTitsRecognition
public import ThirteenPlanes.FiniteGroup.Lifts

@[expose] public section

set_option backward.privateInPublic true

/-! The faithful elementary abelian action and its one-dimensional character spaces
on the concrete compact first-Tits realization. -/

namespace ThirteenPlanes.Graded

open scoped BigOperators
open AlbertLean.Generic.C1Coordinates

noncomputable section

private theorem dot_comm (x y : Charge) : chargeDot x y = chargeDot y x := by
  simp only [chargeDot, mul_comm]

private theorem dot_add_left (x y z : Charge) : chargeDot (x + y) z = chargeDot x z + chargeDot y z := by
  simp [chargeDot, add_mul, Finset.sum_add_distrib]

private theorem dot_add_right (x y z : Charge) : chargeDot x (y + z) = chargeDot x y + chargeDot x z := by
  simp [chargeDot, mul_add, Finset.sum_add_distrib]

private theorem dot_neg_right (x y : Charge) : chargeDot x (-y) = -chargeDot x y := by
  rw [dot_comm x (-y), chargeDot_neg_left, dot_comm y x]

/-- Multiplication by the grading character on each of the 27 complex coordinates. -/
def characterAction (s : Charge) : (Charge → ℂ) ≃ₗ[ℂ] (Charge → ℂ) where
  toFun z q := chargePhase (chargeDot s q) * z q
  invFun z q := chargePhase (chargeDot (-s) q) * z q
  left_inv z := funext fun q => by
    change chargePhase (chargeDot (-s) q) * (chargePhase (chargeDot s q) * z q) = z q
    rw [← mul_assoc, ← chargePhase_add, chargeDot_neg_left, neg_add_cancel, chargePhase_zero, one_mul]
  right_inv z := funext fun q => by
    change chargePhase (chargeDot s q) * (chargePhase (chargeDot (-s) q) * z q) = z q
    rw [← mul_assoc, ← chargePhase_add, chargeDot_neg_left, add_neg_cancel, chargePhase_zero, one_mul]
  map_add' x y := funext fun q => by
    change _ * (x q + y q) = _ * x q + _ * y q
    exact mul_add _ _ _
  map_smul' a z := funext fun q => by
    change _ * (a * z q) = a * (_ * z q)
    exact mul_left_comm _ _ _

@[simp] theorem characterAction_apply (s : Charge) (z : Charge → ℂ) (q : Charge) :
    characterAction s z q = chargePhase (chargeDot s q) * z q := rfl

@[simp] theorem characterAction_zero (z : Charge → ℂ) : characterAction 0 z = z := by
  ext q
  simp [chargeDot]

theorem characterAction_add (s t : Charge) (z : Charge → ℂ) :
    characterAction (s + t) z = characterAction s (characterAction t z) := by
  ext q
  simp only [characterAction_apply, dot_add_left, chargePhase_add, mul_assoc]

/-- The actual common complex character line of each grade. -/
def characterLine (q : Charge) : Submodule ℂ (Charge → ℂ) :=
  ℂ ∙ chargeBasisVector q

theorem characterLine_dimension (q : Charge) : Module.finrank ℂ (characterLine q) = 1 := by
  apply finrank_span_singleton
  intro hz
  have hq := congrFun hz q
  simp [chargeBasisVector] at hq

private theorem characterAction_basis (s q : Charge) :
    characterAction s (chargeBasisVector q) = chargePhase (chargeDot s q) • chargeBasisVector q := by
  funext i
  simp only [characterAction_apply, chargeBasisVector, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst i
    rfl
  · simp

theorem mem_characterLine_iff (q : Charge) (z : Charge → ℂ) :
    z ∈ characterLine q ↔
      ∀ s : Charge, characterAction s z = chargePhase (chargeDot s q) • z := by
  constructor
  · rintro h s
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
    rw [map_smul, characterAction_basis, smul_comm]
  · intro h
    refine Submodule.mem_span_singleton.mpr ⟨z q, ?_⟩
    funext i
    by_cases hi : i = q
    · subst i
      simp [chargeBasisVector]
    · have hzero : z i = 0 := by
        by_contra hne
        apply hi
        funext j
        have hs := congrFun (h (Pi.single j (1 : ZMod 3))) i
        change chargePhase (chargeDot (Pi.single j 1) i) * z i =
          chargePhase (chargeDot (Pi.single j 1) q) * z i at hs
        rw [dot_comm (Pi.single j 1) i, dot_comm (Pi.single j 1) q,
          chargeDot_single, chargeDot_single] at hs
        exact FiniteGroup.chargePhase_injective (mul_right_cancel₀ hne hs)
      simp [chargeBasisVector, hi, hzero]

private theorem characterAction_real (s : Charge) (z : SignedUnital) :
    characterAction s z.val ∈ signedUnitalSubspace := by
  intro q
  simp only [characterAction_apply, dot_neg_right, chargePhase_neg, z.property q,
    star_mul, mul_comm]

/-- The character action restricted to the compact real form in signed coordinates. -/
def realCharacterAction (s : Charge) : SignedUnital ≃ₗ[ℝ] SignedUnital where
  toFun z := ⟨characterAction s z.val, characterAction_real s z⟩
  invFun z := ⟨characterAction (-s) z.val, characterAction_real (-s) z⟩
  left_inv z := Subtype.ext (by
    change characterAction (-s) (characterAction s z.val) = z.val
    rw [← characterAction_add, neg_add_cancel, characterAction_zero])
  right_inv z := Subtype.ext (by
    change characterAction s (characterAction (-s) z.val) = z.val
    rw [← characterAction_add, add_neg_cancel, characterAction_zero])
  map_add' x y := Subtype.ext ((characterAction s).map_add x.val y.val)
  map_smul' r x := Subtype.ext (by
    funext q
    change chargePhase (chargeDot s q) * (r • x.val q) =
      r • (chargePhase (chargeDot s q) * x.val q)
    rw [Complex.real_smul, Complex.real_smul, mul_left_comm])

@[simp] theorem realCharacterAction_apply (s : Charge) (z : SignedUnital) (q : Charge) :
    (realCharacterAction s z).val q = chargePhase (chargeDot s q) * z.val q := rfl

theorem realCharacterAction_product (s : Charge) (x y : SignedUnital) :
    realCharacterAction s (signedUnitalProduct x y) =
      signedUnitalProduct (realCharacterAction s x) (realCharacterAction s y) := by
  apply Subtype.ext
  funext q
  rw [realCharacterAction_apply, signedUnitalProduct_coordinates, signedUnitalProduct_coordinates]
  simp only [Finset.mul_sum, realCharacterAction_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : q = a + b
  · subst q
    simp only [ite_true, dot_add_right, chargePhase_add]
    ring
  · simp [h]

theorem realCharacterAction_one (s : Charge) :
    realCharacterAction s signedUnitalOne = signedUnitalOne := by
  apply Subtype.ext
  funext q
  rw [realCharacterAction_apply]
  by_cases hq : q = 0
  · subst q
    simp [chargeDot]
  · change _ * chargeBasisVector 0 q = chargeBasisVector 0 q
    simp [chargeBasisVector, hq]

private def unitalNativeEquiv : SignedUnital ≃ₗ[ℝ] Glennie.Albert :=
  signedUnitalEquiv.trans nativeCompactTitsEquiv.symm.toLinearEquiv

/-- The grading action on the full native real Albert algebra. -/
def nativeCharacterAction (s : Charge) : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert :=
  unitalNativeEquiv.symm.trans ((realCharacterAction s).trans unitalNativeEquiv)

private theorem compact_unitalNativeEquiv (x : SignedUnital) :
    nativeCompactTitsEquiv (unitalNativeEquiv x) = signedUnitalEquiv x := by
  simp [unitalNativeEquiv]

private theorem unitalNativeEquiv_product (x y : SignedUnital) :
    unitalNativeEquiv (signedUnitalProduct x y) =
      Glennie.jordan (unitalNativeEquiv x) (unitalNativeEquiv y) := by
  apply nativeCompactTitsEquiv.injective
  simpa only [compact_unitalNativeEquiv, nativeCompactTitsEquiv_product] using
    signedUnitalEquiv_product x y

private theorem unitalNativeEquiv_one :
    unitalNativeEquiv signedUnitalOne = (1 : Glennie.Albert) := by
  apply nativeCompactTitsEquiv.injective
  rw [compact_unitalNativeEquiv, signedUnitalEquiv_one, nativeCompactTitsEquiv_one]

private theorem nativeCharacterAction_unitalNativeEquiv (s : Charge) (x : SignedUnital) :
    nativeCharacterAction s (unitalNativeEquiv x) = unitalNativeEquiv (realCharacterAction s x) := by
  simp only [nativeCharacterAction, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem nativeCharacterAction_product (s : Charge) (x y : Glennie.Albert) :
    nativeCharacterAction s (Glennie.jordan x y) =
      Glennie.jordan (nativeCharacterAction s x) (nativeCharacterAction s y) := by
  obtain ⟨a, rfl⟩ := unitalNativeEquiv.surjective x
  obtain ⟨b, rfl⟩ := unitalNativeEquiv.surjective y
  rw [← unitalNativeEquiv_product, nativeCharacterAction_unitalNativeEquiv,
    realCharacterAction_product, unitalNativeEquiv_product, nativeCharacterAction_unitalNativeEquiv,
    nativeCharacterAction_unitalNativeEquiv]

theorem nativeCharacterAction_one (s : Charge) :
    nativeCharacterAction s (1 : Glennie.Albert) = 1 := by
  rw [← unitalNativeEquiv_one, nativeCharacterAction_unitalNativeEquiv, realCharacterAction_one]

theorem nativeCharacterAction_trace (s : Charge) (x : Glennie.Albert) :
    Glennie.trace (nativeCharacterAction s x) = Glennie.trace x := by
  obtain ⟨a, rfl⟩ := unitalNativeEquiv.surjective x
  rw [nativeCharacterAction_unitalNativeEquiv, ← nativeCompactTitsEquiv_trace,
    ← nativeCompactTitsEquiv_trace (unitalNativeEquiv a), compact_unitalNativeEquiv,
    compact_unitalNativeEquiv, signedUnitalEquiv_trace, signedUnitalEquiv_trace]
  simp [chargeDot]

theorem nativeCharacterAction_zero (x : Glennie.Albert) : nativeCharacterAction 0 x = x := by
  obtain ⟨a, rfl⟩ := unitalNativeEquiv.surjective x
  rw [nativeCharacterAction_unitalNativeEquiv]
  congr 1
  exact Subtype.ext (characterAction_zero a.val)

theorem nativeCharacterAction_add (s t : Charge) (x : Glennie.Albert) :
    nativeCharacterAction (s + t) x = nativeCharacterAction s (nativeCharacterAction t x) := by
  obtain ⟨a, rfl⟩ := unitalNativeEquiv.surjective x
  simp only [nativeCharacterAction_unitalNativeEquiv]
  congr 1
  exact Subtype.ext (characterAction_add s t a.val)

private def realPair (g : Charge) : SignedUnital :=
  ⟨chargeBasisVector g + chargeBasisVector (-g), by
    intro q
    have h₁ : -q = g ↔ q = -g := neg_eq_iff_eq_neg
    have h₂ : -q = -g ↔ q = g := neg_inj
    simp [chargeBasisVector, h₁, h₂, add_comm]⟩

/-- Different group elements give different native automorphisms. -/
theorem nativeCharacterAction_injective : Function.Injective nativeCharacterAction := by
  intro s t h
  funext j
  let e : Charge := Pi.single j 1
  have he : e ≠ -e := by
    intro hh
    have he' := congrFun hh j
    simp [e] at he'
    exact (by decide : (1 : ZMod 3) ≠ -1) he'
  let a := realPair e
  have ha : a.val e = 1 := by simp [a, realPair, chargeBasisVector, he]
  have hp := congrArg (fun f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert => f (unitalNativeEquiv a)) h
  simp only [nativeCharacterAction_unitalNativeEquiv] at hp
  have hz := congrArg (fun z : SignedUnital => z.val e) (unitalNativeEquiv.injective hp)
  apply FiniteGroup.chargePhase_injective
  simpa only [realCharacterAction_apply, ha, mul_one, e, chargeDot_single] using hz

/-- Real signed coordinates on the native full Albert algebra, compatible with its complex action. -/
def nativeSignedCoordinates : Glennie.Albert ≃ₗ[ℝ] SignedUnital :=
  unitalNativeEquiv.symm

@[simp] theorem nativeSignedCoordinates_signedNative (x : SignedField) :
    nativeSignedCoordinates (signedNativeEquiv x : Glennie.Albert) = signedUnitalExtend x := by
  apply unitalNativeEquiv.injective
  simp only [nativeSignedCoordinates, LinearEquiv.apply_symm_apply]
  apply nativeCompactTitsEquiv.injective
  rw [compact_unitalNativeEquiv, signedUnitalEquiv_extend]
  exact congrArg Subtype.val (nativeTracelessCompactEquiv_signedNativeEquiv x)

@[simp] theorem nativeSignedCoordinates_one :
    nativeSignedCoordinates (1 : Glennie.Albert) = signedUnitalOne := by
  rw [← unitalNativeEquiv_one, nativeSignedCoordinates, LinearEquiv.symm_apply_apply]

theorem nativeCharacterAction_coordinates (s : Charge) (x : Glennie.Albert) :
    (nativeSignedCoordinates (nativeCharacterAction s x)).val =
      characterAction s (nativeSignedCoordinates x).val := by
  obtain ⟨a, rfl⟩ := unitalNativeEquiv.surjective x
  rw [nativeCharacterAction_unitalNativeEquiv]
  simp only [nativeSignedCoordinates, LinearEquiv.symm_apply_apply]
  rfl

/-- The coordinate action is an actual homomorphism from the additive ternary grade space. -/
def nativeGradingHom : Multiplicative Charge →* (Glennie.Albert ≃ₗ[ℝ] Glennie.Albert) where
  toFun s := nativeCharacterAction s.toAdd
  map_one' := LinearEquiv.ext nativeCharacterAction_zero
  map_mul' s t := LinearEquiv.ext (nativeCharacterAction_add s.toAdd t.toAdd)

theorem nativeGradingHom_injective : Function.Injective nativeGradingHom :=
  fun _ _ h => Multiplicative.toAdd.injective (nativeCharacterAction_injective h)

/-- The native compact algebra has the explicit faithful three-parameter grading action,
and the complex common eigenspaces have dimension one. -/
theorem nativeTernaryGrading :
    Function.Injective nativeCharacterAction ∧
    (∀ s t x, nativeCharacterAction (s + t) x = nativeCharacterAction s (nativeCharacterAction t x)) ∧
    (∀ s x y, nativeCharacterAction s (Glennie.jordan x y) =
      Glennie.jordan (nativeCharacterAction s x) (nativeCharacterAction s y)) ∧
    (∀ s, nativeCharacterAction s (1 : Glennie.Albert) = 1) ∧
    (∀ s x, Glennie.trace (nativeCharacterAction s x) = Glennie.trace x) ∧
    (∀ q : Charge, Module.finrank ℂ (characterLine q) = 1 ∧
      ∀ z : Charge → ℂ, z ∈ characterLine q ↔
        ∀ s : Charge, characterAction s z = chargePhase (chargeDot s q) • z) :=
  ⟨nativeCharacterAction_injective, nativeCharacterAction_add, nativeCharacterAction_product,
    nativeCharacterAction_one, nativeCharacterAction_trace, fun q =>
      ⟨characterLine_dimension q, mem_characterLine_iff q⟩⟩

end

end ThirteenPlanes.Graded
