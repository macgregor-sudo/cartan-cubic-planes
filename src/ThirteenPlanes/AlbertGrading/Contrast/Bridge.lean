module

public import ThirteenPlanes.AlbertGrading.Contrast.QutritTable
public import ThirteenPlanes.AlbertGrading.Tits.Product
public import ThirteenPlanes.NativeTits
public import ThirteenPlanes.NativeFrames

@[expose] public section

/-! Contrast formulas on the native Albert algebra
and its first Tits coordinates.

The centered span of a frame agrees with `nativeFramePlane` in the traceless part, and unbiasedness
is the overlap condition of `TightNativeCode`. The complexification of the compact algebra
is identified with `FirstTits ℂ`. The identification preserves the Jordan product and trace form
and carries the real conjugation to the compact involution. -/

open scoped Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Contrast Contrast.AlbertC Tits

namespace Contrast

/-! ## 1. The plane of a frame -/

/-- `U_F` as used here is the native frame plane, included in `J`. -/
theorem framePlane_eq_native {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    framePlane p = (nativeFramePlane p).map (LinearMap.ker Glennie.traceLinear).subtype := by
  apply le_antisymm
  · rw [framePlane, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    let c : Fin 3 → ℝ := fun b => (if b = a then 1 else 0) - 1 / 3
    have hc : ∑ b, c b = 0 := by
      simp only [c, Fin.sum_univ_three]; fin_cases a <;> norm_num
    obtain ⟨u, hu⟩ := nativeFrameEntries_surjective_of_zero_sum c hc
    refine ⟨nativeFrameChart p u, ⟨u, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply]
    rw [nativeFrameChart_coe hp, hu]
    change ∑ b, c b • p b = _
    rw [← hp.sum_unit]
    fin_cases a <;> simp [c, Fin.sum_univ_three] <;> module
  · rintro _ ⟨x, ⟨u, rfl⟩, rfl⟩
    simp only [Submodule.subtype_apply]
    rw [nativeFrameChart_coe hp]
    exact sum_mem_framePlane p _ (nativeFrameEntries_sum u)

/-- Unbiasedness is the overlap condition of `TightNativeCode`. -/
theorem unbiased_iff_inner (p q : Fin 3 → Glennie.Albert) :
    Unbiased p q ↔ ∀ a b, Glennie.inner (p a) (q b) = 1 / 3 := Iff.rfl

end Contrast

/-- Fourier contrast identities with the native frame plane and overlap form. -/
theorem frameContrast_native :
    (∀ p : Fin 3 → Glennie.Albert, Glennie.Frame p →
      jordan (contrast p) (contrast p) = conj (contrast p) ∧
      jordan (contrast p) (conj (contrast p)) = ofReal 1 ∧
      pair (contrast p) (contrast p) = 0 ∧
      pair (contrast p) (conj (contrast p)) = 3 ∧
      (∀ a : Fin 3, ofReal (p a) = (1 / 3 : ℂ) • (ofReal 1 + chargePhase (-outcome a) • contrast p +
        chargePhase (outcome a) • conj (contrast p))) ∧
      (∀ z : AlbertC,
        (z.re ∈ (nativeFramePlane p).map (LinearMap.ker Glennie.traceLinear).subtype ∧
          z.im ∈ (nativeFramePlane p).map (LinearMap.ker Glennie.traceLinear).subtype) ↔
        z ∈ Submodule.span ℂ {contrast p, conj (contrast p)}) ∧
      (∀ σ : Equiv.Perm (Fin 3), ∃ ζ ∈ mu3,
        contrast (p ∘ σ) = ζ • contrast p ∨ contrast (p ∘ σ) = ζ • conj (contrast p))) ∧
    (∀ p q : Fin 3 → Glennie.Albert, Glennie.Frame p → Glennie.Frame q →
      ((∀ a b, Glennie.inner (p a) (q b) = 1 / 3) ↔
        pair (contrast p) (contrast q) = 0 ∧ pair (contrast p) (conj (contrast q)) = 0)) := by
  obtain ⟨h1, h2⟩ := frameContrast
  refine ⟨fun p hp => ?_, fun p q hp hq => h2 p q hp hq⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1 p hp
  exact ⟨a1, a2, a3, a4, a5, by rw [← framePlane_eq_native hp]; exact a6, a7⟩

/-- Qutrit contrast table with unbiasedness written as the overlap condition. -/
theorem qutritContrastTable_inner (h3 : FrameProperties.QutritFourFrames) :
    ∀ Q : Submodule ℝ Glennie.Albert, (1 : Glennie.Albert) ∈ Q →
      (∀ x y, x ∈ Q → y ∈ Q → Glennie.jordan x y ∈ Q) →
      (∃ I : Graded.FullHermitian3 ≃ₗ[ℝ] Q,
        ∀ X Y, (I (Graded.fullHermitianProduct X Y)).val = Glennie.jordan (I X).val (I Y).val) →
      ∀ F : Fin 4 → Fin 3 → Glennie.Albert, (∀ i, Glennie.Frame (F i)) → (∀ i a, F i a ∈ Q) →
        (∀ i j, i ≠ j → ∀ a b, Glennie.inner (F i a) (F j b) = 1 / 3) →
        ∃ (u : WeylLabel → AlbertC) (lab : Fin 4 → WeylLabel),
          u 0 = ofReal 1 ∧ (∀ v, u (-v) = conj (u v)) ∧
          (∀ i, lab i ≠ 0 ∧ u (lab i) = contrast (F i)) ∧
          (∀ v, v ≠ 0 → ∃ i, v = lab i ∨ v = -lab i) ∧
          (∀ v w, ∃ c : ℂ, c ≠ 0 ∧ jordan (u v) (u w) = c • u (v + w) ∧
            (Dependent v w → c = 1) ∧
            (¬ Dependent v w → c ∈ (fun ζ => -(1 / 2 : ℂ) * ζ) '' mu3)) :=
  qutritContrastTable h3

namespace Contrast

/-! ## 2. The complexification -/

/-- The accepted polarized product on `FirstTits ℂ`. -/
abbrev tProd (x y : FirstTits ℂ) : FirstTits ℂ := polarProduct firstTitsSquare x y

theorem toTau_tProd (x y : FirstTits ℂ) :
    AlbertLean.Generic.TitsLinear.toTau (R := ℂ) (tProd x y) =
      AlbertLean.Generic.TitsLinear.toTau x * AlbertLean.Generic.TitsLinear.toTau y :=
  AlbertLean.Generic.TitsSquare.toTau_polarProduct x y

theorem tProd_add_left (x y z : FirstTits ℂ) : tProd (x + y) z = tProd x z + tProd y z := by
  apply (AlbertLean.Generic.TitsLinear.toTau (R := ℂ)).injective
  rw [map_add, toTau_tProd, toTau_tProd, toTau_tProd, map_add, add_mul]

theorem tProd_add_right (x y z : FirstTits ℂ) : tProd x (y + z) = tProd x y + tProd x z := by
  apply (AlbertLean.Generic.TitsLinear.toTau (R := ℂ)).injective
  rw [map_add, toTau_tProd, toTau_tProd, toTau_tProd, map_add, mul_add]

theorem tProd_smul_left (c : ℂ) (x y : FirstTits ℂ) : tProd (c • x) y = c • tProd x y := by
  apply (AlbertLean.Generic.TitsLinear.toTau (R := ℂ)).injective
  rw [map_smul, toTau_tProd, toTau_tProd, map_smul, smul_mul_assoc]

theorem tProd_smul_right (c : ℂ) (x y : FirstTits ℂ) : tProd x (c • y) = c • tProd x y := by
  apply (AlbertLean.Generic.TitsLinear.toTau (R := ℂ)).injective
  rw [map_smul, toTau_tProd, toTau_tProd, map_smul, mul_smul_comm]

theorem tProd_expand (A B C D : FirstTits ℂ) :
    tProd (A + Complex.I • B) (C + Complex.I • D) =
      tProd A C - tProd B D + Complex.I • (tProd A D + tProd B C) := by
  rw [tProd_add_left, tProd_add_right, tProd_add_right, tProd_smul_left, tProd_smul_left,
    tProd_smul_right, tProd_smul_right, smul_smul, Complex.I_mul_I]
  module

/-- `x + i y ↦ x + i y` in the coordinates, through `nativeCompactTitsEquiv`. -/
def toFT (z : AlbertC) : FirstTits ℂ :=
  CompactTits.coordinates (nativeCompactTitsEquiv z.re) +
    Complex.I • CompactTits.coordinates (nativeCompactTitsEquiv z.im)

/-- The inverse in first Tits coordinates uses the real and imaginary parts. -/
def ofFT (w : FirstTits ℂ) : AlbertC :=
  ⟨nativeCompactTitsEquiv.symm (realPart w), nativeCompactTitsEquiv.symm (imagPart w)⟩

theorem coordinates_realPart (w : FirstTits ℂ) :
    CompactTits.coordinates (realPart w) = (1 / 2 : ℂ) • (w + compactInvolution w) := rfl

theorem coordinates_imagPart (w : FirstTits ℂ) :
    CompactTits.coordinates (imagPart w) = (-Complex.I / 2) • (w - compactInvolution w) := rfl

theorem compactInvolution_toFT (z : AlbertC) :
    compactInvolution (toFT z) = CompactTits.coordinates (nativeCompactTitsEquiv z.re) -
      Complex.I • CompactTits.coordinates (nativeCompactTitsEquiv z.im) := by
  rw [toFT, map_add, compactInvolution_complex_smul, CompactTits.fixed, CompactTits.fixed,
    Complex.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]

theorem realPart_toFT (z : AlbertC) : realPart (toFT z) = nativeCompactTitsEquiv z.re := by
  apply CompactTits.ext
  rw [coordinates_realPart, compactInvolution_toFT, toFT]
  module

theorem imagPart_toFT (z : AlbertC) : imagPart (toFT z) = nativeCompactTitsEquiv z.im := by
  apply CompactTits.ext
  rw [coordinates_imagPart, compactInvolution_toFT, toFT]
  linear_combination (norm := module)
    ((-1 : ℂ) * Complex.I_sq) • CompactTits.coordinates (nativeCompactTitsEquiv z.im)

theorem ofFT_toFT (z : AlbertC) : ofFT (toFT z) = z := by
  apply AlbertC.ext
  · simp [ofFT, realPart_toFT]
  · simp [ofFT, imagPart_toFT]

theorem toFT_ofFT (w : FirstTits ℂ) : toFT (ofFT w) = w := by
  simp only [toFT, ofFT, LinearIsometryEquiv.apply_symm_apply]
  rw [coordinates_realPart, coordinates_imagPart]
  linear_combination (norm := module) ((-1 / 2 : ℂ) * Complex.I_sq) • (w - compactInvolution w)

theorem toFT_add (z w : AlbertC) : toFT (z + w) = toFT z + toFT w := by
  simp only [toFT, add_re, add_im, map_add, smul_add]; abel

theorem toFT_smul (c : ℂ) (z : AlbertC) : toFT (c • z) = c • toFT z := by
  have hr : ∀ (r : ℝ) (x : Glennie.Albert),
      CompactTits.coordinates (nativeCompactTitsEquiv (r • x)) =
        (r : ℂ) • CompactTits.coordinates (nativeCompactTitsEquiv x) := by
    intro r x
    rw [map_smul, map_smul, Complex.coe_smul]
  simp only [toFT, smul_re, smul_im, map_sub, map_add, hr]
  conv_rhs => rw [← Complex.re_add_im c]
  linear_combination (norm := module)
    (-(c.im : ℂ) * Complex.I_sq) • CompactTits.coordinates (nativeCompactTitsEquiv z.im)

/-- `J_ℂ` (pairs) is complex-linearly the complex first Tits algebra. -/
def albertCEquiv : AlbertC ≃ₗ[ℂ] FirstTits ℂ where
  toFun := toFT
  invFun := ofFT
  map_add' := toFT_add
  map_smul' := toFT_smul
  left_inv := ofFT_toFT
  right_inv := toFT_ofFT

theorem coordinates_native_jordan (a b : Glennie.Albert) :
    CompactTits.coordinates (nativeCompactTitsEquiv (Glennie.jordan a b)) =
      tProd (CompactTits.coordinates (nativeCompactTitsEquiv a))
        (CompactTits.coordinates (nativeCompactTitsEquiv b)) := by
  rw [nativeCompactTitsEquiv_product, CompactTits.coordinates_product_eq_polar]

/-- The isomorphism carries the product of `J_ℂ` to the polarized product. -/
theorem albertCEquiv_jordan (z w : AlbertC) :
    albertCEquiv (jordan z w) = tProd (albertCEquiv z) (albertCEquiv w) := by
  change toFT (jordan z w) = tProd (toFT z) (toFT w)
  rw [toFT, toFT, toFT, tProd_expand]
  simp only [jordan_re, jordan_im, map_sub, map_add, coordinates_native_jordan]

/-- The isomorphism respects the explicit first Tits product `(5-tits)`. -/
theorem albertCEquiv_firstTitsJordanProduct (z w : AlbertC) :
    albertCEquiv (jordan z w) = firstTitsJordanProduct (albertCEquiv z) (albertCEquiv w) := by
  rw [albertCEquiv_jordan, firstTitsJordanProduct_eq_polar]

theorem albertCEquiv_one : albertCEquiv (ofReal 1) = firstTitsOne := by
  change toFT (ofReal 1) = firstTitsOne
  simp [toFT, nativeCompactTitsEquiv_one, CompactTits.coordinates_one]

theorem albertCEquiv_ofReal (x : Glennie.Albert) :
    albertCEquiv (ofReal x) = CompactTits.coordinates (nativeCompactTitsEquiv x) := by
  change toFT (ofReal x) = _
  simp [toFT]

/-- The real forms correspond: `conj` on `J_ℂ` is the compact involution. -/
theorem albertCEquiv_conj (z : AlbertC) :
    albertCEquiv (conj z) = compactInvolution (albertCEquiv z) := by
  change toFT (conj z) = compactInvolution (toFT z)
  rw [compactInvolution_toFT, toFT, conj_re, conj_im, map_neg, map_neg, smul_neg,
    ← sub_eq_add_neg]

/-- The first Tits map `complexify f` agrees with complex linear extension through the isomorphism. -/
theorem complexify_albertCEquiv (f : CompactTits →ₗ[ℝ] CompactTits) (z : AlbertC) :
    complexify f (albertCEquiv z) =
      albertCEquiv ⟨nativeCompactTitsEquiv.symm (f (nativeCompactTitsEquiv z.re)),
        nativeCompactTitsEquiv.symm (f (nativeCompactTitsEquiv z.im))⟩ := by
  change complexify f (toFT z) = toFT _
  rw [complexify, realPart_toFT, imagPart_toFT]
  simp only [toFT, LinearIsometryEquiv.apply_symm_apply]

/-- Through the `toTau`, `J_ℂ` is the generic Albert algebra `TauCeti.AlbertAlgebra ℂ`. -/
theorem toTau_albertCEquiv_jordan (z w : AlbertC) :
    AlbertLean.Generic.TitsLinear.toTau (R := ℂ) (albertCEquiv (jordan z w)) =
      AlbertLean.Generic.TitsLinear.toTau (albertCEquiv z) *
        AlbertLean.Generic.TitsLinear.toTau (albertCEquiv w) := by
  rw [albertCEquiv_jordan, toTau_tProd]

theorem toTau_albertCEquiv_one :
    AlbertLean.Generic.TitsLinear.toTau (R := ℂ) (albertCEquiv (ofReal 1)) = 1 := by
  rw [albertCEquiv_one, AlbertLean.Generic.TitsLinear.toTau_firstTitsOne]

end Contrast

end

end ThirteenPlanes.AlbertGrading
