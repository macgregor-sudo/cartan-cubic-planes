module

public import ThirteenPlanes.Cartan.AlbertDerivationRank
public import ThirteenPlanes.Cartan.LieComplexification
public import ThirteenPlanes.AlbertGrading.Grading.Complexification
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

set_option backward.privateInPublic true

/-! Real and complex derivations of the actual compact Albert product. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading
open scoped RealInnerProductSpace TensorProduct

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The linear Leibniz law is closed under the operator commutator. -/
def productDerivations {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (p : V →ₗ[R] V →ₗ[R] V) : LieSubalgebra R (Module.End R V) where
  carrier := {D | ∀ x y, D (p x y) = p (D x) y + p x (D y)}
  zero_mem' := by intro x y; simp
  add_mem' := by
    intro D E hD hE x y
    change D (p x y) + E (p x y) = p (D x + E x) y + p x (D y + E y)
    rw [hD x y, hE x y, map_add, LinearMap.add_apply, map_add]
    abel
  smul_mem' := by
    intro r D hD x y
    change r • D (p x y) = p (r • D x) y + p x (r • D y)
    rw [hD x y, map_smul, LinearMap.smul_apply, map_smul, smul_add]
  lie_mem' := by
    intro D E hD hE x y
    change D (E (p x y)) - E (D (p x y)) =
      p (D (E x) - E (D x)) y + p x (D (E y) - E (D y))
    change ∀ x y, D (p x y) = p (D x) y + p x (D y) at hD
    change ∀ x y, E (p x y) = p (E x) y + p x (E y) at hE
    simp only [hD, hE, map_add, map_sub, LinearMap.sub_apply]
    abel

/-- The literal real derivation Lie subalgebra on the compact Albert carrier. -/
def nativeAlbertDerivations : LieSubalgebra ℝ (Module.End ℝ Glennie.Albert) :=
  productDerivations albertJordan.L

abbrev NativeAlbertDerivations := ↥nativeAlbertDerivations

/-- The literal complex derivation Lie subalgebra on the complexified Albert carrier. -/
def jcJordanProduct : JC →ₗ[ℂ] JC →ₗ[ℂ] JC :=
  LinearMap.mk₂ ℂ JC.mul JC.mul_add_left JC.mul_smul_left JC.mul_add_right JC.mul_smul_right

@[simp] theorem jcJordanProduct_apply (x y : JC) : jcJordanProduct x y = JC.mul x y := rfl

def complexAlbertDerivations : LieSubalgebra ℂ (Module.End ℂ JC) :=
  productDerivations jcJordanProduct

abbrev ComplexAlbertDerivations := ↥complexAlbertDerivations

@[simp] theorem mem_nativeAlbertDerivations {D : Module.End ℝ Glennie.Albert} :
    D ∈ nativeAlbertDerivations ↔ albertJordan.IsDerivation D := Iff.rfl

set_option maxHeartbeats 800000 in
@[simp] theorem mem_complexAlbertDerivations {D : Module.End ℂ JC} :
    D ∈ complexAlbertDerivations ↔
      ∀ x y, D (JC.mul x y) = JC.mul (D x) y + JC.mul x (D y) := by
  change (∀ x y, D (jcJordanProduct x y) = jcJordanProduct (D x) y + jcJordanProduct x (D y)) ↔ _
  simp only [jcJordanProduct_apply]

theorem nativeAlbertDerivation_skew (D : NativeAlbertDerivations) : IsSkew D.val :=
  albertDerivation_isSkew D.property

/-- The real derivations have exactly the same underlying operators as the trace-skew model. -/
def nativeAlbertDerivationSkewEquiv : NativeAlbertDerivations ≃ₗ[ℝ] albertJordan.skewDerivations where
  toFun D := ⟨⟨D.val, nativeAlbertDerivation_skew D⟩, D.property⟩
  invFun D := ⟨D.val.val, D.property⟩
  left_inv D := Subtype.ext rfl
  right_inv D := Subtype.ext (Subtype.ext rfl)
  map_add' D E := Subtype.ext (Subtype.ext rfl)
  map_smul' r D := Subtype.ext (Subtype.ext rfl)

theorem nativeAlbertDerivations_finrank : Module.finrank ℝ NativeAlbertDerivations = 52 :=
  nativeAlbertDerivationSkewEquiv.finrank_eq.trans
    (albertDerivationEquiv.finrank_eq.trans AlbertSequential.finrank_albertDerivation)

private def jcRealCoordinate : JC →ₗ[ℝ] Glennie.Albert where
  toFun := JC.re
  map_add' := JC.add_re
  map_smul' := JC.real_smul_re

private def jcImagCoordinate : JC →ₗ[ℝ] Glennie.Albert where
  toFun := JC.im
  map_add' := JC.add_im
  map_smul' := JC.real_smul_im

/-- Real part of the restriction of a complex derivation to the real algebra. -/
def complexDerivationRealPart (D : ComplexAlbertDerivations) : NativeAlbertDerivations :=
  ⟨jcRealCoordinate.comp ((D.val.restrictScalars ℝ).comp JC.ofLinear), by
    apply mem_nativeAlbertDerivations.mpr
    intro x y
    have h := congrArg JC.re ((mem_complexAlbertDerivations.mp D.property) (JC.of x) (JC.of y))
    rw [JC.of_mul] at h
    change (D.val (JC.of (Glennie.jordan x y))).re =
      Glennie.jordan (D.val (JC.of x)).re y + Glennie.jordan x (D.val (JC.of y)).re
    simpa using h⟩

/-- Imaginary part of the restriction of a complex derivation to the real algebra. -/
def complexDerivationImagPart (D : ComplexAlbertDerivations) : NativeAlbertDerivations :=
  ⟨jcImagCoordinate.comp ((D.val.restrictScalars ℝ).comp JC.ofLinear), by
    apply mem_nativeAlbertDerivations.mpr
    intro x y
    have h := congrArg JC.im ((mem_complexAlbertDerivations.mp D.property) (JC.of x) (JC.of y))
    rw [JC.of_mul] at h
    change (D.val (JC.of (Glennie.jordan x y))).im =
      Glennie.jordan (D.val (JC.of x)).im y + Glennie.jordan x (D.val (JC.of y)).im
    simpa using h⟩

@[simp] theorem complexDerivationRealPart_apply (D : ComplexAlbertDerivations) (x : Glennie.Albert) :
    (complexDerivationRealPart D).val x = (D.val (JC.of x)).re := rfl

@[simp] theorem complexDerivationImagPart_apply (D : ComplexAlbertDerivations) (x : Glennie.Albert) :
    (complexDerivationImagPart D).val x = (D.val (JC.of x)).im := rfl

/-- A real derivation extends by acting on both components of the native complexification. -/
def extendAlbertDerivation : NativeAlbertDerivations →ₗ[ℝ] ComplexAlbertDerivations where
  toFun D := ⟨JC.mapC D.val, by
    have h (x y : Glennie.Albert) :
        D.val (Glennie.jordan x y) = Glennie.jordan (D.val x) y + Glennie.jordan x (D.val y) :=
      D.property x y
    apply mem_complexAlbertDerivations.mpr
    intro x y
    apply JC.ext <;> simp only [JC.mapC_re, JC.mapC_im, JC.mul_re, JC.mul_im, JC.add_re,
      JC.add_im, map_sub, map_add, h] <;> abel⟩
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply JC.ext <;> rfl
  map_smul' r D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply JC.ext
    · change r • D.val x.re = (r • (JC.mapC D.val x)).re
      rw [JC.real_smul_re, JC.mapC_re]
    · change r • D.val x.im = (r • (JC.mapC D.val x)).im
      rw [JC.real_smul_im, JC.mapC_im]

@[simp] theorem extendAlbertDerivation_val (D : NativeAlbertDerivations) :
    (extendAlbertDerivation D).val = JC.mapC D.val := rfl

private theorem extendAlbertDerivation_lie (D E : NativeAlbertDerivations) :
    extendAlbertDerivation ⁅D, E⁆ = ⁅extendAlbertDerivation D, extendAlbertDerivation E⁆ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply JC.ext <;> rfl

theorem jc_endomorphism_ext (D E : Module.End ℂ JC) (h : ∀ x : Glennie.Albert, D (JC.of x) = E (JC.of x)) :
    D = E := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [JC.eq_re_add_im x]
  conv_rhs => rw [JC.eq_re_add_im x]
  simp only [map_add, map_smul, h]

def albertDerivationComplexMap : LieComplex NativeAlbertDerivations →ₗ[ℂ] ComplexAlbertDerivations :=
  extendAlbertDerivation.liftBaseChange ℂ

@[simp] theorem albertDerivationComplexMap_tmul (z : ℂ) (D : NativeAlbertDerivations) :
    albertDerivationComplexMap (z ⊗ₜ[ℝ] D) = z • extendAlbertDerivation D := rfl

@[simp] theorem albertDerivationComplexMap_ofReal (D : NativeAlbertDerivations) :
    albertDerivationComplexMap (LieComplex.ofReal D) = extendAlbertDerivation D := by simp

private theorem albertDerivationComplexMap_parts (x : LieComplex NativeAlbertDerivations) :
    albertDerivationComplexMap x =
      extendAlbertDerivation (LieComplex.realPart x) + Complex.I • extendAlbertDerivation (LieComplex.imagPart x) := by
  simpa only [map_add, map_smul, albertDerivationComplexMap_ofReal] using
    congrArg albertDerivationComplexMap (LieComplex.decompose_smul x).symm

@[simp] theorem realPart_albertDerivationComplexMap (x : LieComplex NativeAlbertDerivations) :
    complexDerivationRealPart (albertDerivationComplexMap x) = LieComplex.realPart x := by
  rw [albertDerivationComplexMap_parts]
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  simp [JC.mapC_of]

@[simp] theorem imagPart_albertDerivationComplexMap (x : LieComplex NativeAlbertDerivations) :
    complexDerivationImagPart (albertDerivationComplexMap x) = LieComplex.imagPart x := by
  rw [albertDerivationComplexMap_parts]
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  simp [JC.mapC_of]

theorem complexAlbertDerivation_decompose (D : ComplexAlbertDerivations) :
    extendAlbertDerivation (complexDerivationRealPart D) +
      Complex.I • extendAlbertDerivation (complexDerivationImagPart D) = D := by
  apply Subtype.ext
  apply jc_endomorphism_ext
  intro x
  change (JC.mapC (complexDerivationRealPart D).val +
    Complex.I • JC.mapC (complexDerivationImagPart D).val) (JC.of x) = _
  rw [LinearMap.add_apply, LinearMap.smul_apply, JC.mapC_of, JC.mapC_of]
  exact (JC.eq_re_add_im (D.val (JC.of x))).symm

private theorem albertDerivationComplexMap_bijective : Function.Bijective albertDerivationComplexMap := by
  constructor
  · intro x y h
    have hr := congrArg complexDerivationRealPart h
    have hi := congrArg complexDerivationImagPart h
    simp only [realPart_albertDerivationComplexMap] at hr
    simp only [imagPart_albertDerivationComplexMap] at hi
    calc
      x = _ := (LieComplex.decompose x).symm
      _ = _ := by rw [hr, hi]
      _ = y := LieComplex.decompose y
  · intro D
    refine ⟨LieComplex.ofReal (complexDerivationRealPart D) +
      Complex.I • LieComplex.ofReal (complexDerivationImagPart D), ?_⟩
    simpa only [map_add, map_smul, albertDerivationComplexMap_ofReal] using complexAlbertDerivation_decompose D

private theorem albertDerivationComplexMap_lie (x y : LieComplex NativeAlbertDerivations) :
    albertDerivationComplexMap ⁅x, y⁆ = ⁅albertDerivationComplexMap x, albertDerivationComplexMap y⁆ := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ =>
    have h : ⁅x₁ + x₂, y⁆ = ⁅x₁, y⁆ + ⁅x₂, y⁆ := add_lie _ _ _
    rw [h, map_add, hx₁, hx₂, map_add, add_lie]
  | tmul z D =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ =>
      have h : ⁅z ⊗ₜ[ℝ] D, y₁ + y₂⁆ = ⁅z ⊗ₜ[ℝ] D, y₁⁆ + ⁅z ⊗ₜ[ℝ] D, y₂⁆ :=
        LieRing.lie_add (z ⊗ₜ[ℝ] D : LieComplex NativeAlbertDerivations) y₁ y₂
      rw [h, map_add, hy₁, hy₂, map_add, lie_add]
    | tmul w E =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, albertDerivationComplexMap_tmul,
        albertDerivationComplexMap_tmul, albertDerivationComplexMap_tmul,
        extendAlbertDerivation_lie, smul_lie, lie_smul, mul_smul]

/-- All derivations of the native complex product are the complexification of the
real compact Albert derivations, including their operator commutator. -/
def albertDerivationComplexEquiv : LieComplex NativeAlbertDerivations ≃ₗ⁅ℂ⁆ ComplexAlbertDerivations :=
  { LinearEquiv.ofBijective albertDerivationComplexMap albertDerivationComplexMap_bijective with
    map_lie' := fun {x y} => albertDerivationComplexMap_lie x y }

@[simp] theorem albertDerivationComplexEquiv_apply_ofReal (D : NativeAlbertDerivations) :
    albertDerivationComplexEquiv (LieComplex.ofReal D) = extendAlbertDerivation D :=
  albertDerivationComplexMap_ofReal D

theorem complexAlbertDerivations_finrank : Module.finrank ℂ ComplexAlbertDerivations = 52 := by
  rw [← albertDerivationComplexEquiv.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange.trans nativeAlbertDerivations_finrank

end

end ThirteenPlanes.Cartan
