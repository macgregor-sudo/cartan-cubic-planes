module

public import ThirteenPlanes.Cartan.AlbertOperators
public import AlbertDerivationDimension
public import CompanionIltyakovAction

@[expose] public section

set_option backward.privateInPublic true

/-! The dimension of the actual trace-skew Albert derivation algebra. -/

namespace ThirteenPlanes.Cartan

open scoped RealInnerProductSpace

noncomputable section

private abbrev nativeCoordinates := AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv

private theorem albertLeftTrace (x : Glennie.Albert) :
    LinearMap.trace ℝ Glennie.Albert (albertJordan.L x) = 9 * albertJordan.trace x := by
  have hconj : nativeCoordinates.symm.conj (albertJordan.L x) =
      AlbertSequential.nativeJordanProductLinear (nativeCoordinates.symm x) := by
    apply LinearMap.ext
    intro y
    apply nativeCoordinates.injective
    change nativeCoordinates (nativeCoordinates.symm (Glennie.jordan x (nativeCoordinates y))) =
      nativeCoordinates (AlbertSequential.jordanMul (nativeCoordinates.symm x) y)
    rw [nativeCoordinates.apply_symm_apply,
      AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_jordanMul,
      nativeCoordinates.apply_symm_apply]
  rw [← LinearMap.trace_conj' (albertJordan.L x) nativeCoordinates.symm, hconj,
    AlbertSequential.CompanionIltyakov.native_leftTrace_eq_nine, albertJordan_trace,
    ← AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_trace,
    nativeCoordinates.apply_symm_apply]

/-- Every native real Albert derivation is automatically trace-skew. -/
theorem albertDerivation_isSkew {D : Module.End ℝ Glennie.Albert} (hD : albertJordan.IsDerivation D) :
    IsSkew D := by
  have ht (x : Glennie.Albert) : albertJordan.trace (D x) = 0 := by
    have h := albertLeftTrace (D x)
    rw [← albertJordan.bracket_leftMul hD, operatorBracket, map_sub,
      LinearMap.trace_mul_comm ℝ D, sub_self] at h
    linarith
  intro x y
  have h := ht (albertJordan.L x y)
  rw [hD, map_add, albertJordan.trace_product, albertJordan.trace_product] at h
  linarith

private theorem albertDerivation_native_iff (D : Module.End ℝ Glennie.Albert) :
    albertJordan.IsDerivation D ↔ nativeCoordinates.symm.conj D ∈ AlbertSequential.albertDerivations := by
  constructor
  · intro h x y
    apply nativeCoordinates.injective
    change nativeCoordinates (nativeCoordinates.symm (D (nativeCoordinates (AlbertSequential.jordanMul x y)))) =
      nativeCoordinates (AlbertSequential.jordanMul (nativeCoordinates.symm (D (nativeCoordinates x))) y +
        AlbertSequential.jordanMul x (nativeCoordinates.symm (D (nativeCoordinates y))))
    simp only [map_add, nativeCoordinates.apply_symm_apply,
      AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_jordanMul]
    exact h _ _
  · intro h x y
    let E : AlbertSequential.AlbertDerivation := ⟨nativeCoordinates.symm.conj D, h⟩
    have hp := AlbertSequential.albertDerivation_mul E (nativeCoordinates.symm x) (nativeCoordinates.symm y)
    have hp' := congrArg nativeCoordinates hp
    change nativeCoordinates (nativeCoordinates.symm (D (nativeCoordinates
      (AlbertSequential.jordanMul (nativeCoordinates.symm x) (nativeCoordinates.symm y))))) =
      nativeCoordinates (AlbertSequential.jordanMul
        (nativeCoordinates.symm (D (nativeCoordinates (nativeCoordinates.symm x))))
        (nativeCoordinates.symm y) + AlbertSequential.jordanMul (nativeCoordinates.symm x)
        (nativeCoordinates.symm (D (nativeCoordinates (nativeCoordinates.symm y))))) at hp'
    simp only [map_add, nativeCoordinates.apply_symm_apply,
      AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_jordanMul] at hp'
    exact hp'

/-- The native trace-skew Albert derivations have real dimension 52. -/
def albertDerivationEquiv : albertJordan.skewDerivations ≃ₗ[ℝ] AlbertSequential.AlbertDerivation where
  toFun D := ⟨nativeCoordinates.symm.conj D.val.val, (albertDerivation_native_iff D.val.val).mp D.property⟩
  invFun E := by
    let D := nativeCoordinates.conj E.val
    have hh : nativeCoordinates.symm.conj D = E.val := nativeCoordinates.conj.symm_apply_apply E.val
    have hD := (albertDerivation_native_iff D).mpr (hh.symm ▸ E.property)
    exact ⟨⟨D, albertDerivation_isSkew hD⟩, hD⟩
  left_inv D := Subtype.ext (Subtype.ext (nativeCoordinates.symm.conj.symm_apply_apply D.val.val))
  right_inv E := by
    apply Subtype.ext
    change nativeCoordinates.symm.conj (nativeCoordinates.conj E.val) = E.val
    exact nativeCoordinates.conj.symm_apply_apply E.val
  map_add' A B := Subtype.ext (nativeCoordinates.symm.conj.map_add A.val.val B.val.val)
  map_smul' r A := Subtype.ext (nativeCoordinates.symm.conj.map_smul r A.val.val)

/- The classical dimension 52 of the Albert derivations is given by the description
in Baez, The Octonions, §4.1, Eq. (19), and Yokota, Exceptional Lie Groups,
Theorem 2.10.2. This theorem establishes the dimension of the concrete operator space. -/
theorem albertDerivationOperators_finrank : Module.finrank ℝ albertDerivationOperators = 52 := by
  rw [LinearMap.finrank_range_of_inj albertJordan.restrictDerivation_injective]
  exact albertDerivationEquiv.finrank_eq.trans AlbertSequential.finrank_albertDerivation

/-- The full Casimir of the compact Albert derivations equals twice the identity. -/
theorem albertFullCasimir_eq_two :
    operatorCasimir albertDerivationOperators = (2 : ℝ) • LinearMap.id := by
  rw [albertFullCasimir, albertDerivationOperators_finrank]
  norm_num

end

end ThirteenPlanes.Cartan
