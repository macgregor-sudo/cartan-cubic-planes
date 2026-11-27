module

public import ThirteenPlanes.SignedTits
public import ThirteenPlanes.SignedSupport
public import ThirteenPlanes.Tits.Metric
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

@[expose] public section

/-!
# Targets for first-Tits grading and Weyl basis and exterior frame normal form (Section 5)

All statements live on the carriers: the complex first-Tits triples
`FirstTits ℂ = M₃(ℂ)³` with the compact conjugation `Tits.compactInvolution` (the paper's `σ`),
the complex bilinear trace form `titsTraceForm` (the paper's `T(,)`), and the compact real form
`Tits.CompactTits` (the paper's `J_T`) with its polarized product `CompactTits.product`.

The paper's product `(5-tits)` is written out literally as `paperProduct`; the adjugate pairing
`a # b` is `sharpPair`. The matrices `X`, `Z` and `D_v = ω^{-ab} X^a Z^b` are written literally;
`ι_k` is `iota`, and `u_g = ι_k(D_v)` is `titsBasis`.

The complexification `J_T ⊗ ℂ` is modelled by `FirstTits ℂ` itself: every `z` is uniquely
`x + i y` with `x, y` fixed by `σ`, and the complex extension of a real-linear map `f` of `J_T` is
`complexify f`.
-/

open scoped Matrix RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-! ## The first Tits construction, as printed -/

/-- The cyclic shift `X e_m = e_{m+1}` on `ℂ³`, indices mod 3. -/
def shiftMatrix : Matrix (ZMod 3) (ZMod 3) ℂ := fun i j => if i = j + 1 then 1 else 0

/-- The clock `Z e_m = ω^m e_m`. -/
def clockMatrix : Matrix (ZMod 3) (ZMod 3) ℂ := fun i j => if i = j then chargePhase i else 0

/-- `D_v = ω^{-ab} X^a Z^b` for `v = (a,b) ∈ 𝔽₃²`. -/
def weylD (v : WeylLabel) : Matrix (ZMod 3) (ZMod 3) ℂ :=
  chargePhase (-(v.1 * v.2)) • (shiftMatrix ^ v.1.val * clockMatrix ^ v.2.val)

/-- `ι_k(a)`: the triple with `a` in position `k` and zeros elsewhere. -/
def iota (k : ZMod 3) (A : Mat3 ℂ) : FirstTits ℂ :=
  (if k = 0 then A else 0, if k = 1 then A else 0, if k = 2 then A else 0)

/-- `u_g = ι_k(D_v)` for `g = (v,k) ∈ 𝔽₃² × 𝔽₃`. -/
def titsBasis (g : Charge) : FirstTits ℂ := iota (g 2) (weylD (g 0, g 1))

/-- `a # b = ab + ba − (tr a) b − (tr b) a + (tr a tr b − tr(ab)) 1`. -/
def sharpPair (a b : Mat3 ℂ) : Mat3 ℂ :=
  a * b + b * a - trace3 a • b - trace3 b • a + (trace3 a * trace3 b - trace3 (a * b)) • (1 : Mat3 ℂ)

/-- The product `x ∘ y = (c₀,c₁,c₂)` of equation `(5-tits)`, term by term. -/
def firstTitsJordanProduct (x y : FirstTits ℂ) : FirstTits ℂ :=
  ((1 / 2 : ℂ) • (x.1 * y.1 + y.1 * x.1) - (1 / 2 : ℂ) • (x.2.1 * y.2.2 + y.2.1 * x.2.2) +
      ((1 / 2 : ℂ) * trace3 (x.2.1 * y.2.2 + y.2.1 * x.2.2)) • (1 : Mat3 ℂ),
    (1 / 2 : ℂ) • sharpPair x.2.2 y.2.2 - (1 / 2 : ℂ) • (x.1 * y.2.1 + y.1 * x.2.1) +
      ((1 / 2 : ℂ) * trace3 x.1) • y.2.1 + ((1 / 2 : ℂ) * trace3 y.1) • x.2.1,
    (1 / 2 : ℂ) • sharpPair x.2.1 y.2.1 - (1 / 2 : ℂ) • (x.2.2 * y.1 + y.2.2 * x.1) +
      ((1 / 2 : ℂ) * trace3 x.1) • y.2.2 + ((1 / 2 : ℂ) * trace3 y.1) • x.2.2)

/-- `Ad_U(a₀,a₁,a₂) = (U a₀ U*, U a₁ U*, U a₂ U*)`. -/
def adMap (U : Mat3 ℂ) (x : FirstTits ℂ) : FirstTits ℂ :=
  (U * x.1 * Uᴴ, U * x.2.1 * Uᴴ, U * x.2.2 * Uᴴ)

/-- `φ(a₀,a₁,a₂) = (a₀, ω a₁, ω² a₂)`. -/
def phiMap (x : FirstTits ℂ) : FirstTits ℂ :=
  (x.1, chargeRoot • x.2.1, (chargeRoot ^ 2) • x.2.2)

/-- `ψ_R(a₀,a₁,a₂) = (a₀, a₁ R, R* a₂)`. -/
def psiMap (R : Mat3 ℂ) (x : FirstTits ℂ) : FirstTits ℂ :=
  (x.1, x.2.1 * R, Rᴴ * x.2.2)

/-! ## Automorphisms, complexification and grading groups of `J_T` -/

/-- An automorphism of `J_T`: a real-linear bijection preserving the product. -/
def IsTitsAutomorphism (f : CompactTits ≃ₗ[ℝ] CompactTits) : Prop :=
  ∀ x y, f (CompactTits.product x y) = CompactTits.product (f x) (f y)

theorem realPart_fixed (z : FirstTits ℂ) :
    compactInvolution ((1 / 2 : ℂ) • (z + compactInvolution z)) =
      (1 / 2 : ℂ) • (z + compactInvolution z) := by
  rw [compactInvolution_complex_smul, map_add, compactInvolution_involutive, add_comm]
  congr 1
  simp [Complex.ext_iff]

theorem imagPart_fixed (z : FirstTits ℂ) :
    compactInvolution ((-Complex.I / 2) • (z - compactInvolution z)) =
      (-Complex.I / 2) • (z - compactInvolution z) := by
  rw [compactInvolution_complex_smul, map_sub, compactInvolution_involutive]
  have h : star (-Complex.I / 2) = -(-Complex.I / 2) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [h, neg_smul, ← smul_neg, neg_sub]

/-- The real part `(z + σ z)/2 ∈ J_T`. -/
def realPart (z : FirstTits ℂ) : CompactTits :=
  CompactTits.ofFixed _ (realPart_fixed z)

/-- The imaginary part `(z − σ z)/(2i) ∈ J_T`. -/
def imagPart (z : FirstTits ℂ) : CompactTits :=
  CompactTits.ofFixed _ (imagPart_fixed z)

/-- The complex-linear extension of a real-linear map of `J_T` to `J_T ⊗ ℂ = FirstTits ℂ`. -/
def complexify (f : CompactTits →ₗ[ℝ] CompactTits) (z : FirstTits ℂ) : FirstTits ℂ :=
  CompactTits.coordinates (f (realPart z)) + Complex.I • CompactTits.coordinates (f (imagPart z))

/-- The eigenspace in `J_T ⊗ ℂ` of a character `χ` of a group `E` of linear maps of `J_T`. -/
def characterSpace (E : Subgroup (CompactTits ≃ₗ[ℝ] CompactTits)) (χ : E →* ℂˣ) :
    Set (FirstTits ℂ) :=
  {z | ∀ e : E, complexify (e : CompactTits ≃ₗ[ℝ] CompactTits).toLinearMap z = ((χ e : ℂˣ) : ℂ) • z}

/-- A ternary grading group of `J_T`: a group of automorphisms isomorphic to `(ℤ/3)³` each of whose
characters has a one-dimensional eigenspace on the complexification. -/
def IsTernaryGradingGroup (E : Subgroup (CompactTits ≃ₗ[ℝ] CompactTits)) : Prop :=
  (∀ f ∈ E, IsTitsAutomorphism f) ∧ Nonempty (E ≃* Multiplicative (Fin 3 → ZMod 3)) ∧
    ∀ χ : E →* ℂˣ, ∃ v : FirstTits ℂ, v ≠ 0 ∧
      characterSpace E χ = (Submodule.span ℂ {v} : Set (FirstTits ℂ))

/-- Linear dependence of two vectors of `𝔽₃³`. -/
def F3Dependent (g h : Charge) : Prop :=
  ∃ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) ∧ a • g + b • h = 0

/-! ## Frames of `J_T` -/

/-- A frame of `J_T`: idempotents `p_a` with `p_a ∘ p_b = 0` for `a ≠ b`, `T(p_a) = 1`, `∑ p_a = e`. -/
def IsTitsFrame (p : ZMod 3 → CompactTits) : Prop :=
  (∀ a b, CompactTits.product (p a) (p b) = if a = b then p a else 0) ∧
    (∀ a, CompactTits.trace (p a) = 1) ∧ ∑ a, p a = CompactTits.one

/-- The plane of a frame: the span of the `p_a − e/3`. -/
def titsFramePlane (p : ZMod 3 → CompactTits) : Submodule ℝ CompactTits :=
  Submodule.span ℝ (Set.range fun a => p a - (1 / 3 : ℝ) • CompactTits.one)

/-- `Q₀⁰`: the traceless part of `Q₀ = {(A,0,0)}`. -/
def visibleTraceless : Submodule ℝ CompactTits where
  carrier := {x | (CompactTits.coordinates x).2.1 = 0 ∧ CompactTits.trace x = 0}
  zero_mem' := ⟨by simp, map_zero _⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨by simp [hx, hy], by rw [map_add, hx', hy', add_zero]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    exact ⟨by simp [hx], by rw [map_smul, hx', smul_zero]⟩

/-- The frame `(1, ω^a, ω^{-a})/3` of `J_T`. -/
def exteriorPoint (a : ZMod 3) : CompactTits :=
  CompactTits.ofMatrices ((1 / 3 : ℂ) • (1 : Mat3 ℂ)) (((1 / 3 : ℂ) * chargePhase a) • (1 : Mat3 ℂ))
    (by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      congr 1
      simp)

/-- The contrast `u_f = ∑_a ω^a p_{fa} ∈ J_T ⊗ ℂ`. -/
def titsContrast (p : ZMod 3 → CompactTits) : FirstTits ℂ :=
  ∑ a, chargePhase a • CompactTits.coordinates (p a)

/-! ## The two targets -/

/-- First-Tits grading and Weyl basis, all three parts. -/
def Statements.TitsLemma : Prop :=
  -- (i) `Ad_U` for unitary `U`
  (∀ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
    adMap U firstTitsOne = firstTitsOne ∧
    (∀ x y, titsTraceForm (adMap U x) (adMap U y) = titsTraceForm x y) ∧
    (∀ x y, adMap U (firstTitsJordanProduct x y) = firstTitsJordanProduct (adMap U x) (adMap U y)) ∧
    (∀ x, compactInvolution (adMap U x) = adMap U (compactInvolution x)) ∧
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
      ∀ x, CompactTits.coordinates (f x) = adMap U (CompactTits.coordinates x)) ∧
  -- (i) `φ`
  (phiMap firstTitsOne = firstTitsOne ∧
    (∀ x y, titsTraceForm (phiMap x) (phiMap y) = titsTraceForm x y) ∧
    (∀ x y, phiMap (firstTitsJordanProduct x y) = firstTitsJordanProduct (phiMap x) (phiMap y)) ∧
    (∀ x, compactInvolution (phiMap x) = phiMap (compactInvolution x)) ∧
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
      ∀ x, CompactTits.coordinates (f x) = phiMap (CompactTits.coordinates x)) ∧
  -- (i) `ψ_R` for `R ∈ SU(3)`
  (∀ R ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ,
    psiMap R firstTitsOne = firstTitsOne ∧
    (∀ x y, titsTraceForm (psiMap R x) (psiMap R y) = titsTraceForm x y) ∧
    (∀ x y, psiMap R (firstTitsJordanProduct x y) = firstTitsJordanProduct (psiMap R x) (psiMap R y)) ∧
    (∀ x, compactInvolution (psiMap R x) = psiMap R (compactInvolution x)) ∧
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
      ∀ x, CompactTits.coordinates (f x) = psiMap R (CompactTits.coordinates x)) ∧
  -- (ii)
  titsBasis 0 = firstTitsOne ∧
  (∀ g, compactInvolution (titsBasis g) = titsBasis (-g)) ∧
  (∀ g h, titsTraceForm (titsBasis g) (titsBasis h) = if g + h = 0 then 3 else 0) ∧
  (∀ g h, F3Dependent g h → firstTitsJordanProduct (titsBasis g) (titsBasis h) = titsBasis (g + h)) ∧
  (∀ (v w : WeylLabel) (k l : ZMod 3), ¬ F3Dependent (chargeFrom v k) (chargeFrom w l) →
    firstTitsJordanProduct (titsBasis (chargeFrom v k)) (titsBasis (chargeFrom w l)) =
      (-(1 / 2 : ℂ) * chargePhase (symplecticBracket v w * (l - k))) •
        titsBasis (chargeFrom v k + chargeFrom w l)) ∧
  -- (iii)
  (∀ fZ fX fφ : CompactTits ≃ₗ[ℝ] CompactTits,
    (∀ x, CompactTits.coordinates (fZ x) = adMap clockMatrix (CompactTits.coordinates x)) →
    (∀ x, CompactTits.coordinates (fX x) = adMap shiftMatrix⁻¹ (CompactTits.coordinates x)) →
    (∀ x, CompactTits.coordinates (fφ x) = phiMap (CompactTits.coordinates x)) →
    IsTernaryGradingGroup (Subgroup.closure {fZ, fX, fφ}) ∧
    (∀ χ : Subgroup.closure ({fZ, fX, fφ} : Set (CompactTits ≃ₗ[ℝ] CompactTits)) →* ℂˣ,
      ∃! g : Charge, characterSpace _ χ = (Submodule.span ℂ {titsBasis g} : Set (FirstTits ℂ))) ∧
    (∀ g : Charge, ∃ χ : Subgroup.closure ({fZ, fX, fφ} : Set (CompactTits ≃ₗ[ℝ] CompactTits)) →* ℂˣ,
      characterSpace _ χ = (Submodule.span ℂ {titsBasis g} : Set (FirstTits ℂ))))

/-- Exterior frame normal form. The automorphism `ψ_{V*}` is also recorded to fix `Q₀` pointwise. -/
def Statements.ExteriorFrame : Prop :=
  ∀ p : ZMod 3 → CompactTits, IsTitsFrame p → (titsFramePlane p).IsOrtho visibleTraceless →
    ∃ π : Equiv.Perm (ZMod 3), ∃ V ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ,
      (∀ a, CompactTits.coordinates (p (π a)) =
        (1 / 3 : ℂ) • ((1 : Mat3 ℂ), chargePhase a • V, chargePhase (-a) • Vᴴ)) ∧
      Vᴴ ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ ∧
      (∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
        (∀ x, CompactTits.coordinates (f x) = psiMap Vᴴ (CompactTits.coordinates x)) ∧
        (∀ a, f (p (π a)) = exteriorPoint a) ∧
        (∀ x, (CompactTits.coordinates x).2.1 = 0 → f x = x)) ∧
      IsTitsFrame exteriorPoint ∧
      titsContrast exteriorPoint = ((0 : Mat3 ℂ), (0 : Mat3 ℂ), (1 : Mat3 ℂ))

end

end ThirteenPlanes.AlbertGrading
