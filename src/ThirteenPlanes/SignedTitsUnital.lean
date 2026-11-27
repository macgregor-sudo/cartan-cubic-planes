module

public import ThirteenPlanes.NativeTits

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes

noncomputable section

/-- All 27 charge coordinates in the real form, including the real zero grade. -/
def signedUnitalSubspace : Submodule ℝ (Charge → ℂ) where
  carrier := {z | ∀ q, z (-q) = star (z q)}
  zero_mem' := by intro q; simp
  add_mem' := by
    intro x y hx hy q
    change x (-q) + y (-q) = star (x q + y q)
    rw [hx q, hy q, star_add]
  smul_mem' := by
    intro r x hx q
    change r • x (-q) = star (r • x q)
    rw [hx q, star_smul]
    simp

abbrev SignedUnital := ↥signedUnitalSubspace

private theorem signedUnital_iff_fixed (z : Charge → ℂ) :
    z ∈ signedUnitalSubspace ↔
      Tits.compactInvolution (gradedTitsCoordinates z) = gradedTitsCoordinates z := by
  rw [compactInvolution_gradedTitsCoordinates]
  constructor
  · intro hz
    congr 1
    funext q
    rw [hz q, star_star]
  · intro hz q
    have h := gradedTitsComplexEquiv.injective hz
    simpa only [neg_neg] using (congrFun h (-q)).symm

/-- Real signed coefficients synthesize to the compact first Tits coordinates. -/
def signedUnitalToTits : SignedUnital →ₗ[ℝ] Tits.CompactTits where
  toFun x := Tits.CompactTits.ofFixed (gradedTitsCoordinates x.val)
    ((signedUnital_iff_fixed x.val).mp x.property)
  map_add' x y := Tits.CompactTits.ext (by
    simp only [Tits.CompactTits.coordinates_ofFixed, map_add]
    exact gradedTitsCoordinates.map_add x.val y.val)
  map_smul' r x := Tits.CompactTits.ext (by
    simp only [Tits.CompactTits.coordinates_ofFixed, map_smul]
    exact (gradedTitsCoordinates.restrictScalars ℝ).map_smul r x.val)

@[simp] theorem signedUnitalToTits_coordinates (x : SignedUnital) :
    Tits.CompactTits.coordinates (signedUnitalToTits x) = gradedTitsCoordinates x.val := rfl

/-- The full compact algebra has exactly the real signed charge coordinates. -/
def signedUnitalEquiv : SignedUnital ≃ₗ[ℝ] Tits.CompactTits := by
  refine LinearEquiv.ofBijective signedUnitalToTits ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (gradedTitsComplexEquiv.injective
      (congrArg Tits.CompactTits.coordinates h))
  · intro y
    let z := gradedTitsComplexEquiv.symm (Tits.CompactTits.coordinates y)
    have hz : gradedTitsCoordinates z = Tits.CompactTits.coordinates y :=
      gradedTitsComplexEquiv.apply_symm_apply _
    have hz' : z ∈ signedUnitalSubspace := (signedUnital_iff_fixed z).mpr (by
      rw [hz, Tits.CompactTits.fixed])
    exact ⟨⟨z, hz'⟩, Tits.CompactTits.ext hz⟩

theorem signedUnital_finrank : Module.finrank ℝ SignedUnital = 27 :=
  signedUnitalEquiv.finrank_eq.trans compactTits_finrank

/-- The same charge-additive product restricts to the real signed locus. -/
def signedUnitalProduct (x y : SignedUnital) : SignedUnital :=
  ⟨gradedProduct x.val y.val, (signedUnital_iff_fixed _).mpr (by
    change Tits.compactInvolution (gradedTitsComplexEquiv (gradedProduct x.val y.val)) =
      gradedTitsComplexEquiv (gradedProduct x.val y.val)
    rw [gradedTitsComplexEquiv_product]
    have h := Tits.CompactTits.coordinates_product_eq_polar (signedUnitalEquiv x) (signedUnitalEquiv y)
    change Tits.CompactTits.coordinates _ = polarProduct firstTitsSquare
      (gradedTitsComplexEquiv x.val) (gradedTitsComplexEquiv y.val) at h
    rw [← h, Tits.CompactTits.fixed])⟩

theorem signedUnitalProduct_coordinates (x y : SignedUnital) (q : Charge) :
    (signedUnitalProduct x y).val q =
      ∑ i, ∑ j, if q = i+j then gradedProductCoefficient i j * x.val i * y.val j else 0 := by
  change gradedProduct x.val y.val q = _
  simp [gradedProduct, chargeBasisVector, mul_ite, Pi.smul_apply, smul_eq_mul]

/-- The grade-zero coefficient vector is the real signed unit. -/
def signedUnitalOne : SignedUnital :=
  ⟨chargeBasisVector 0, (signedUnital_iff_fixed _).mpr (by
    rw [gradedTitsCoordinates_unit, ← Tits.CompactTits.coordinates_one, Tits.CompactTits.fixed])⟩

theorem signedUnitalEquiv_product (x y : SignedUnital) :
    signedUnitalEquiv (signedUnitalProduct x y) =
      Tits.CompactTits.product (signedUnitalEquiv x) (signedUnitalEquiv y) := by
  apply Tits.CompactTits.ext
  rw [Tits.CompactTits.coordinates_product_eq_polar]
  exact gradedTitsComplexEquiv_product x.val y.val

@[simp] theorem signedUnitalEquiv_one : signedUnitalEquiv signedUnitalOne = Tits.CompactTits.one :=
  Tits.CompactTits.ext (by rw [Tits.CompactTits.coordinates_one]; exact gradedTitsCoordinates_unit)

@[simp] theorem signedUnitalProduct_one (x : SignedUnital) :
    signedUnitalProduct x signedUnitalOne = x := by
  apply signedUnitalEquiv.injective
  rw [signedUnitalEquiv_product, signedUnitalEquiv_one]
  obtain ⟨y, hy⟩ := nativeCompactTitsEquiv.surjective (signedUnitalEquiv x)
  rw [← hy, ← nativeCompactTitsEquiv_one, ← nativeCompactTitsEquiv_product]
  simp

@[simp] theorem signedUnitalProduct_one_left (x : SignedUnital) :
    signedUnitalProduct signedUnitalOne x = x := by
  apply signedUnitalEquiv.injective
  rw [signedUnitalEquiv_product, signedUnitalEquiv_one]
  obtain ⟨y, hy⟩ := nativeCompactTitsEquiv.surjective (signedUnitalEquiv x)
  rw [← hy, ← nativeCompactTitsEquiv_one, ← nativeCompactTitsEquiv_product, Glennie.jordan_comm]
  simp

/-- The original real fields are the zero coefficient subspace of the unital presentation. -/
def signedUnitalExtend (x : SignedField) : SignedUnital :=
  ⟨signedExtend x, signedExtend_neg x⟩

@[simp] theorem signedUnitalEquiv_extend (x : SignedField) :
    signedUnitalEquiv (signedUnitalExtend x) = (gradedTitsEquiv x).val := rfl

@[simp] theorem signedUnitalEquiv_trace (x : SignedUnital) :
    Tits.CompactTits.trace (signedUnitalEquiv x) = 3 * (x.val 0).re := by
  rw [Tits.CompactTits.trace_apply]
  change (trace3 (gradedTitsCoordinates x.val).1).re = _
  rw [gradedTitsCoordinates_trace]
  simp [Complex.mul_re]

/-- The unital pairing also includes the zero-grade term with weight three. -/
theorem signedUnitalEquiv_inner (x y : SignedUnital) :
    ((⟪signedUnitalEquiv x, signedUnitalEquiv y⟫ : ℝ) : ℂ) =
      3 * ∑ q, x.val q * star (y.val q) := by
  rw [Tits.CompactTits.complexTrace_eq_inner]
  change titsTraceForm (gradedTitsCoordinates x.val) (gradedTitsCoordinates y.val) = _
  rw [gradedTitsCoordinates_traceForm]
  have hy (q : Charge) : y.val (-q) = star (y.val q) := y.property q
  simp only [hy]

end

end ThirteenPlanes
