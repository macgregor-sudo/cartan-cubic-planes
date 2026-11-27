module

public import ThirteenPlanes.Cartan.DerivationGradingCompactness
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

set_option backward.privateInPublic true

/-! Invariant positive forms on simple Lie algebras and exchanged products. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.Cartan

noncomputable section

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G]

/-- A symmetric positive-definite invariant real bilinear form. -/
structure IsInvariantPositiveForm (B : LinearMap.BilinForm ℝ G) : Prop where
  symmetric : ∀ x y, B x y = B y x
  positive : ∀ x ≠ 0, 0 < B x x
  invariant : ∀ x y z, B ⁅x, y⁆ z = B x ⁅y, z⁆

theorem IsInvariantPositiveForm.ad_skew {B : LinearMap.BilinForm ℝ G}
    (hB : IsInvariantPositiveForm B) (x y z : G) :
    B ⁅x, y⁆ z = -B y ⁅x, z⁆ := by
  rw [← hB.invariant y x z, ← lie_skew x y, map_neg, LinearMap.neg_apply]

/-- On a real finite-dimensional simple Lie algebra, invariant positive metrics
are proportional by a positive scalar. -/
theorem invariantPositiveForms_eq_mul [FiniteDimensional ℝ G] [LieAlgebra.IsSimple ℝ G]
    {A B : LinearMap.BilinForm ℝ G} (hA : IsInvariantPositiveForm A)
    (hB : IsInvariantPositiveForm B) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, B x y = a * A x y := by
  let : InnerProductSpace.Core ℝ G :=
    { inner := fun x y => A x y
      conj_inner_symm := fun x y => by simpa only [RCLike.conj_to_real] using hA.symmetric y x
      re_inner_nonneg := fun x => by
        change 0 ≤ A x x
        by_cases hx : x = 0
        · subst x
          simp
        · exact (hA.positive x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra hn
        exact (hA.positive x hn).ne' hx }
  let : NormedAddCommGroup G := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ G := InnerProductSpace.ofCore (𝕜 := ℝ) (F := G) inferInstance
  let T : Module.End ℝ G := (SymmetricCubic.riesz (V := G)).comp B
  have pairing (x y : G) : A (T x) y = B x y :=
    SymmetricCubic.inner_riesz (B x) y
  have symm : T.IsSymmetric := by
    intro x y
    change A (T x) y = A x (T y)
    rw [pairing, hA.symmetric x (T y), pairing, hB.symmetric x y]
  have commute (z x : G) : T ⁅z, x⁆ = ⁅z, T x⁆ := by
    apply ext_inner_right ℝ
    intro y
    change A (T ⁅z, x⁆) y = A ⁅z, T x⁆ y
    rw [pairing, hB.ad_skew, hA.ad_skew, pairing]
  let : Nontrivial G := LieAlgebra.IsSimple.nontrivial ℝ G
  let i : Fin (Module.finrank ℝ G) := ⟨0, Module.finrank_pos⟩
  let a : ℝ := symm.eigenvalues rfl i
  let x₀ := symm.eigenvectorBasis rfl i
  let I : LieIdeal ℝ G :=
    { toSubmodule := T.eigenspace a
      lie_mem := fun {z x} hx => by
        apply Module.End.mem_eigenspace_iff.mpr
        rw [commute, Module.End.mem_eigenspace_iff.mp hx, lie_smul] }
  have hx₀ : x₀ ∈ I := (symm.hasEigenvector_eigenvectorBasis rfl i).1
  have hn₀ : x₀ ≠ 0 := (symm.hasEigenvector_eigenvectorBasis rfl i).2
  have hTop : I = ⊤ := (LieAlgebra.IsSimple.eq_bot_or_eq_top I).resolve_left (fun he => by
    rw [he, LieSubmodule.mem_bot] at hx₀
    exact hn₀ hx₀)
  have hEq (x y : G) : B x y = a * A x y := by
    have hx : x ∈ I := hTop ▸ LieSubmodule.mem_top x
    have he : T x = a • x :=
      Module.End.mem_eigenspace_iff.mp (show x ∈ T.eigenspace a from hx)
    rw [← pairing, he, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have ha : 0 < a := by
    have hp := hB.positive x₀ hn₀
    rw [hEq] at hp
    exact pos_of_mul_pos_left hp (hA.positive x₀ hn₀).le
  exact ⟨a, ha, hEq⟩

section ExchangedProduct

variable {H : Type*} [LieRing H] [LieAlgebra ℝ H]
  [LieAlgebra.IsSimple ℝ G]

private theorem product_cross_zero {B : LinearMap.BilinForm ℝ (G × H)}
    (hB : IsInvariantPositiveForm B) (x : G) (y : H) : B (x, 0) (0, y) = 0 := by
  let f : G →ₗ[ℝ] ℝ := (B.flip (0, y)).comp (LinearMap.inl ℝ G H)
  have hbr (u v : G) : f ⁅u, v⁆ = 0 := by
    change B (⁅u, v⁆, (0 : H)) (0, y) = 0
    have h : (⁅u, v⁆, (0 : H)) = ⁅(u, (0 : H)), (v, (0 : H))⁆ := by simp
    rw [h, hB.invariant, show ⁅(v, (0 : H)), ((0 : G), y)⁆ = (0 : G × H) by simp]
    exact map_zero _
  let I : LieIdeal ℝ G :=
    { toSubmodule := LinearMap.ker f
      lie_mem := fun {_ _} _ => LinearMap.mem_ker.mpr (hbr _ _) }
  have hTop : I = ⊤ := (LieAlgebra.IsSimple.eq_bot_or_eq_top I).resolve_left (fun he => by
    apply LieAlgebra.IsSimple.non_abelian ℝ (L := G)
    refine ⟨fun u v => ?_⟩
    have hu : ⁅u, v⁆ ∈ I := LinearMap.mem_ker.mpr (hbr u v)
    rwa [he, LieSubmodule.mem_bot] at hu)
  have hx : x ∈ I := hTop ▸ LieSubmodule.mem_top x
  exact LinearMap.mem_ker.mp hx

/-- Preserving both metrics while exchanging the two factors forces one common scalar. -/
theorem invariantPositiveForms_exchangedProduct_eq_mul [FiniteDimensional ℝ G]
    {A B : LinearMap.BilinForm ℝ (G × H)} (hA : IsInvariantPositiveForm A)
    (hB : IsInvariantPositiveForm B) (e : G ≃ₗ[ℝ] H) (θ : G × H → G × H)
    (hexchange : ∀ x : G, θ (x, 0) = (0, e x))
    (hθA : ∀ x y, A (θ x) (θ y) = A x y)
    (hθB : ∀ x y, B (θ x) (θ y) = B x y) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, B x y = a * A x y := by
  let ι := LinearMap.inl ℝ G H
  have restriction (F : LinearMap.BilinForm ℝ (G × H)) (hF : IsInvariantPositiveForm F) :
      IsInvariantPositiveForm (F.compl₁₂ ι ι) := by
    constructor
    · exact fun x y => hF.symmetric (x, 0) (y, 0)
    · intro x hx
      exact hF.positive (x, 0) (fun he => hx (congrArg Prod.fst he))
    · intro x y z
      change F (⁅x, y⁆, (0 : H)) (z, 0) = F (x, 0) (⁅y, z⁆, (0 : H))
      simpa using hF.invariant (x, 0) (y, 0) (z, (0 : H))
  obtain ⟨a, ha, hleft⟩ := invariantPositiveForms_eq_mul (restriction A hA) (restriction B hB)
  have hl (x y : G) : B (x, 0) (y, 0) = a * A (x, 0) (y, 0) := hleft x y
  have hr (x y : H) : B (0, x) (0, y) = a * A (0, x) (0, y) := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← hexchange, ← hexchange, hθA, hθB, hl]
  have split (F : LinearMap.BilinForm ℝ (G × H)) (hF : IsInvariantPositiveForm F)
      (x y : G × H) : F x y = F (x.1, 0) (y.1, 0) + F (0, x.2) (0, y.2) := by
    conv_lhs => rw [show x = (x.1, 0) + (0, x.2) by simp,
      show y = (y.1, 0) + (0, y.2) by simp]
    simp only [map_add, LinearMap.add_apply, product_cross_zero hF,
      hF.symmetric (0, x.2) (y.1, 0), add_zero, zero_add]
  refine ⟨a, ha, fun x y => ?_⟩
  rw [split B hB, split A hA, hl, hr, mul_add]

end ExchangedProduct

/-- A Lie equivalence transports symmetry, positivity, and invariance of a form. -/
theorem IsInvariantPositiveForm.pullback {H : Type*} [LieRing H] [LieAlgebra ℝ H]
    {B : LinearMap.BilinForm ℝ H} (hB : IsInvariantPositiveForm B) (e : G ≃ₗ⁅ℝ⁆ H) :
    IsInvariantPositiveForm (B.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap) where
  symmetric x y := hB.symmetric (e x) (e y)
  positive x hx := hB.positive (e x) (fun hz => hx (e.injective (hz.trans (map_zero e).symm)))
  invariant x y z := by
    change B (e ⁅x, y⁆) (e z) = B (e x) (e ⁅y, z⁆)
    rw [e.map_lie, e.map_lie, hB.invariant]

/-- Minus the Killing form is an invariant positive metric on a compact Lie algebra. -/
theorem negativeKilling_isInvariantPositive (h : CompactKilling G) :
    IsInvariantPositiveForm (-killingForm ℝ G) where
  symmetric := fun x y => by
    change -killingForm ℝ G x y = -killingForm ℝ G y x
    rw [LieModule.traceForm_comm ℝ G G]
  positive := fun x hx => neg_pos.mpr (h x hx)
  invariant := fun x y z => by
    change -killingForm ℝ G ⁅x, y⁆ z = -killingForm ℝ G x ⁅y, z⁆
    rw [LieModule.traceForm_apply_lie_apply ℝ G G]

end

end ThirteenPlanes.Cartan
