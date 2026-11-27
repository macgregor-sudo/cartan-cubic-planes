module

public import ThirteenPlanes.FiniteGroup.Invariants

@[expose] public section

set_option backward.privateInPublic true

/-! Code-invariant linear and bilinear forms, and symmetry of code-invariant trilinear forms. -/

open Matrix
open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace FiniteGroup

open SignedStabilizer

local notation "z" => signedCoordinates

/-- The complex-bilinear form with a given coefficient table. -/
def biTri (c : NonzeroCharge → NonzeroCharge → ℂ) :
    (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ :=
  (Pi.basisFun ℂ NonzeroCharge).constr ℂ fun i => (Pi.basisFun ℂ NonzeroCharge).constr ℂ fun j =>
    c i j

theorem biTri_apply (c : NonzeroCharge → NonzeroCharge → ℂ) (Z W : NonzeroCharge → ℂ) :
    biTri c Z W = ∑ i, ∑ j, c i j * Z i * W j := by
  simp only [biTri, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem biTri_singles (c : NonzeroCharge → NonzeroCharge → ℂ) (i j : NonzeroCharge) :
    biTri c (Pi.single i 1) (Pi.single j 1) = c i j := by
  rw [biTri_apply]; simp [Pi.single_apply]

/-- The complex-linear functional with a given coefficient table. -/
def linTri (c : NonzeroCharge → ℂ) : (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ :=
  (Pi.basisFun ℂ NonzeroCharge).constr ℂ c

theorem linTri_apply (c : NonzeroCharge → ℂ) (Z : NonzeroCharge → ℂ) :
    linTri c Z = ∑ i, c i * Z i := by
  simp only [linTri, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem linTri_single (c : NonzeroCharge → ℂ) (i : NonzeroCharge) :
    linTri c (Pi.single i 1) = c i := by
  rw [linTri_apply]; simp [Pi.single_apply]

namespace Relabeling

variable (R : Relabeling)

theorem biTable_eq_of_invariant (c : NonzeroCharge → NonzeroCharge → ℂ)
    (hinv : ∀ X Y : SignedField,
      biTri c (R.coordMap (z X)) (R.coordMap (z Y)) = biTri c (z X) (z Y))
    (x y : NonzeroCharge) :
    chargePhase (R.phase x + R.phase y) * c (R.perm x) (R.perm y) = c x y := by
  let T := (biTri c).compl₁₂ R.coordMap R.coordMap - biTri c
  have hT : T = 0 := by
    apply bilinear_ext_of_real
    intro a b
    change biTri c (R.coordMap _) (R.coordMap _) - biTri c _ _ = 0
    rw [hinv, sub_self]
  have h := congrArg (fun T => T (Pi.single x 1) (Pi.single y 1)) hT
  simp only [LinearMap.zero_apply] at h
  change biTri c (R.coordMap _) (R.coordMap _) - biTri c _ _ = 0 at h
  rw [coordMap_single, coordMap_single] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, biTri_singles] at h
  rw [chargePhase_add]
  linear_combination h

theorem linTable_eq_of_invariant (c : NonzeroCharge → ℂ)
    (hinv : ∀ X : SignedField, linTri c (R.coordMap (z X)) = linTri c (z X))
    (x : NonzeroCharge) :
    chargePhase (R.phase x) * c (R.perm x) = c x := by
  let T := linTri c ∘ₗ R.coordMap - linTri c
  have hT : T = 0 := by
    apply linear_ext_of_real
    intro a
    change linTri c (R.coordMap _) - linTri c _ = 0
    rw [hinv, sub_self]
  have h := congrArg (fun T => T (Pi.single x 1)) hT
  simp only [LinearMap.zero_apply] at h
  change linTri c (R.coordMap _) - linTri c _ = 0 at h
  rw [coordMap_single] at h
  simp only [map_smul, smul_eq_mul, linTri_single] at h
  linear_combination h

end Relabeling

private def ofRealL : ℝ →ₗ[ℝ] ℂ := Complex.ofRealCLM.toLinearMap

section Bilinear

variable (b : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ)

private def bc (X : SignedField) (k : NonzeroCharge) : ℂ := fcoef (ofRealL ∘ₗ b X) k

private def bl (k : NonzeroCharge) : SignedField →ₗ[ℝ] ℂ where
  toFun X := bc b X k
  map_add' X X' := by
    simp only [bc, fcoef, ofRealL, LinearMap.comp_apply, map_add, LinearMap.add_apply,
      ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply]
    ring
  map_smul' r X := by
    simp only [bc, fcoef, ofRealL, LinearMap.comp_apply, map_smul, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul,
      RingHom.id_apply, Complex.real_smul]
    ring

/-- The complex coefficient table of a real bilinear form. -/
def biTableOf (i k : NonzeroCharge) : ℂ := fcoef (bl b k) i

theorem bilinear_eq_biTri (X Y : SignedField) : (b X Y : ℂ) = biTri (biTableOf b) (z X) (z Y) := by
  rw [biTri_apply]
  have h2 : (b X Y : ℂ) = ∑ k, bc b X k * z Y k := functional_eq_sum (ofRealL ∘ₗ b X) Y
  have h1 : ∀ k, bc b X k = ∑ i, biTableOf b i k * z X i := fun k => functional_eq_sum (bl b k) X
  rw [h2]
  simp only [h1, Finset.sum_mul]
  exact Finset.sum_comm

end Bilinear

/-- Code invariance of a real bilinear form. -/
def IsCodeInvariant₂ (b : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ) : Prop :=
  ∀ (A : SpecialLinearGroup (Fin 3) (ZMod 3)) (F : Charge → ZMod 3) (hF : IsOddPhase F),
    (codeRelabeling A F hF).PreservesCubic → ∀ X Y : SignedField,
      b ((codeRelabeling A F hF).toIsometry X) ((codeRelabeling A F hF).toIsometry Y) = b X Y

/-- Code invariance of a real linear functional. -/
def IsCodeInvariant₁ (l : SignedField →ₗ[ℝ] ℝ) : Prop :=
  ∀ (A : SpecialLinearGroup (Fin 3) (ZMod 3)) (F : Charge → ZMod 3) (hF : IsOddPhase F),
    (codeRelabeling A F hF).PreservesCubic → ∀ X : SignedField,
      l ((codeRelabeling A F hF).toIsometry X) = l X

private theorem chargeAct_one' (x : NonzeroCharge) : chargeAct 1 x = x :=
  Subtype.ext (by simp [chargeAct_val])

private theorem coordOdd (k : Fin 3) : IsOddPhase (fun v : Charge => v k) := fun v => by simp

private theorem coordinate_preserves (k : Fin 3) :
    (codeRelabeling 1 (fun v : Charge => v k) (coordOdd k)).PreservesCubic :=
  (codeRelabeling_preserves_iff 1 _ (coordOdd k)).mpr (fun a b _ => by simp)

private theorem phase_kill {a : ZMod 3} (ha : a ≠ 0) {t : ℂ} (h : chargePhase a * t = t) : t = 0 := by
  have hne : chargePhase a ≠ 1 := fun e => ha (chargePhase_injective (e.trans chargePhase_zero.symm))
  have : (chargePhase a - 1) * t = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- A code-invariant real linear functional on the signed carrier vanishes. -/
theorem codeInvariant_linear {l : SignedField →ₗ[ℝ] ℝ} (hl : IsCodeInvariant₁ l) : l = 0 := by
  have hc : ∀ x, fcoef (ofRealL ∘ₗ l) x = 0 := by
    intro x
    obtain ⟨k, hk⟩ : ∃ k, x.val k ≠ 0 := by
      by_contra h
      apply x.property
      funext m
      by_contra hm
      exact h ⟨m, hm⟩
    have hp := coordinate_preserves k
    have e := (codeRelabeling 1 (fun v : Charge => v k) (coordOdd k)).linTable_eq_of_invariant
      (fcoef (ofRealL ∘ₗ l)) (fun X => by
        rw [← Relabeling.coord_toLinearMap, linTri_apply, linTri_apply,
          ← functional_eq_sum, ← functional_eq_sum]
        have := hl 1 _ (coordOdd k) hp X
        simp only [Relabeling.toIsometry_apply] at this
        simp only [ofRealL, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          Complex.ofRealCLM_apply, this]) x
    change chargePhase (x.val k) * fcoef _ (chargeAct 1 x) = _ at e
    rw [chargeAct_one'] at e
    exact phase_kill hk e
  ext X
  have := functional_eq_sum (ofRealL ∘ₗ l) X
  rw [Finset.sum_eq_zero (fun x _ => by rw [hc x, zero_mul])] at this
  have h2 : ((l X : ℝ) : ℂ) = 0 := this
  simpa using h2

/-- A code-invariant real bilinear form on the signed carrier is a multiple of the inner product. -/
theorem codeInvariant_bilinear {b : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ}
    (hb : IsCodeInvariant₂ b) : ∃ a : ℝ, ∀ X Y : SignedField, b X Y = a * ⟪X, Y⟫ := by
  set T := biTableOf b with hTdef
  have heq : ∀ (A : SpecialLinearGroup (Fin 3) (ZMod 3)) (F : Charge → ZMod 3) (hF : IsOddPhase F),
      (codeRelabeling A F hF).PreservesCubic → ∀ x y : NonzeroCharge,
        chargePhase (F x.val + F y.val) * T (chargeAct A x) (chargeAct A y) = T x y := by
    intro A F hF hp x y
    exact (codeRelabeling A F hF).biTable_eq_of_invariant T (fun X Y => by
      rw [← Relabeling.coord_toLinearMap, ← Relabeling.coord_toLinearMap, ← bilinear_eq_biTri,
        ← bilinear_eq_biTri]
      have := hb A F hF hp X Y
      simp only [Relabeling.toIsometry_apply] at this
      rw [this]) x y
  -- support on opposite pairs
  have hsupp : ∀ x y : NonzeroCharge, x.val + y.val ≠ 0 → T x y = 0 := by
    intro x y hs
    obtain ⟨k, hk⟩ : ∃ k, (x.val + y.val) k ≠ 0 := by
      by_contra h
      apply hs
      funext m
      by_contra hm
      exact h ⟨m, hm⟩
    have e := heq 1 (fun v : Charge => v k) (coordOdd k) (coordinate_preserves k) x y
    rw [chargeAct_one', chargeAct_one'] at e
    exact phase_kill hk e
  -- constancy on opposite pairs
  let d : NonzeroCharge := ⟨Pi.single 0 1, by decide⟩
  have hconst : ∀ x : NonzeroCharge, T x (oppositeCharge x) = T d (oppositeCharge d) := by
    intro x
    obtain ⟨A, hA⟩ := sl_transitive d.property x.property
    obtain ⟨F, hF, hp⟩ := codeLift_exists A
    have e := heq A F hF hp d (oppositeCharge d)
    have h1 : chargeAct A d = x := Subtype.ext hA
    have h2 : chargeAct A (oppositeCharge d) = oppositeCharge x := by
      apply Subtype.ext
      change (A : ChargeMatrix) *ᵥ (-d.val) = -x.val
      rw [Matrix.mulVec_neg, hA]
    rw [h1, h2] at e
    change chargePhase (F d.val + F (-d.val)) * _ = _ at e
    rw [hF, add_neg_cancel, chargePhase_zero, one_mul] at e
    exact e
  set γ := T d (oppositeCharge d)
  refine ⟨γ.re / 3, fun X Y => ?_⟩
  have h := bilinear_eq_biTri b X Y
  rw [biTri_apply, ← hTdef] at h
  have hrow : ∀ i, ∑ j, T i j * z X i * z Y j = γ * z X i * z Y (oppositeCharge i) := by
    intro i
    rw [Finset.sum_eq_single (oppositeCharge i)]
    · rw [hconst]
    · intro j _ hj
      rw [hsupp i j, zero_mul, zero_mul]
      intro hs
      apply hj
      apply Subtype.ext
      change j.val = -i.val
      linear_combination hs
    · simp
  simp only [hrow] at h
  have hinner : ∑ i, γ * z X i * z Y (oppositeCharge i) = γ * ((⟪Y, X⟫ / 3 : ℝ) : ℂ) := by
    rw [← biForm_real, biForm_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hinner] at h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.re_mul_ofReal] at hre
  rw [hre, real_inner_comm]
  ring

/-- Code-invariant real trilinear forms are fully symmetric. -/
theorem codeInvariant_trilinear_symmetric
    {f : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ} (hf : IsCodeInvariant f)
    (X Y W : SignedField) : f X Y W = f Y X W ∧ f X Y W = f X W Y := by
  obtain ⟨a, b, hab⟩ := codeInvariant_trilinear hf
  rw [hab, hab, hab]
  constructor
  · rw [signedPair.diagonalCubic.apply_swap₁₂ X Y W, signedPair.mixingCubic.apply_swap₁₂ X Y W]
  · rw [signedPair.diagonalCubic.apply_swap₂₃ X Y W, signedPair.mixingCubic.apply_swap₂₃ X Y W]

/-- Code-invariant real bilinear forms are symmetric. -/
theorem codeInvariant_bilinear_symmetric {b : SignedField →ₗ[ℝ] SignedField →ₗ[ℝ] ℝ}
    (hb : IsCodeInvariant₂ b) (X Y : SignedField) : b X Y = b Y X := by
  obtain ⟨a, ha⟩ := codeInvariant_bilinear hb
  rw [ha, ha, real_inner_comm]

end FiniteGroup

end

end ThirteenPlanes
