module

public import ThirteenPlanes.Cartan.ComplexOperators
public import ThirteenPlanes.SignedFields
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

@[expose] public section

set_option backward.privateInPublic true

/-! Homogeneous derivations of a Jordan algebra with a normalized ternary basis. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan

noncomputable section

/-- The homogeneous basis given by the normalized character vectors of an Albert grading. -/
structure NormalizedTernaryBasis (A : Type*) [AddCommGroup A] [Module ℂ A] where
  basis : Basis Charge ℂ A
  product : A →ₗ[ℂ] A →ₗ[ℂ] A
  unit_left : ∀ x, product (basis 0) x = x
  comm : ∀ x y, product x y = product y x
  homogeneous_product : ∀ g h, ∃ c : ℂ, product (basis g) (basis h) = c • basis (g + h)
  square : ∀ g, g ≠ 0 → product (basis g) (basis g) = basis (-g)
  opposite : ∀ g, g ≠ 0 → product (basis g) (basis (-g)) = basis 0
  independent_product : ∀ g h, g ≠ 0 → h ≠ 0 → h ≠ g → h ≠ -g →
    product (basis g) (basis h) ≠ 0

namespace NormalizedTernaryBasis

variable {A : Type*} [AddCommGroup A] [Module ℂ A]
variable (M : NormalizedTernaryBasis A)

theorem charge_double_eq_neg (g : Charge) : g + g = -g := by
  funext i
  change g i + g i = -g i
  have h : (3 : ZMod 3) = 0 := by decide
  linear_combination g i * h

/-- A complex-linear derivation for the specified bilinear Jordan product. -/
def IsDerivation (D : Module.End ℂ A) : Prop :=
  ∀ x y, D (M.product x y) = M.product (D x) y + M.product x (D y)

/-- A homogeneous operator shifts every character line by the same charge. -/
def HasDegree (D : Module.End ℂ A) (γ : Charge) : Prop :=
  ∀ g, ∃ c : ℂ, D (M.basis g) = c • M.basis (g + γ)

/-- The complex subspace of derivations of the given degree. -/
def derivationGrade (γ : Charge) : Submodule ℂ (Module.End ℂ A) where
  carrier := {D | M.IsDerivation D ∧ M.HasDegree D γ}
  zero_mem' := ⟨by intro x y; simp, fun g => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro D E ⟨hD, d⟩ ⟨hE, e⟩
    refine ⟨?_, ?_⟩
    · intro x y
      simp only [LinearMap.add_apply, hD x y, hE x y, map_add]
      abel
    · intro g
      obtain ⟨a, ha⟩ := d g
      obtain ⟨b, hb⟩ := e g
      exact ⟨a + b, by simp only [LinearMap.add_apply, ha, hb, add_smul]⟩
  smul_mem' := by
    rintro a D ⟨hD, d⟩
    refine ⟨?_, ?_⟩
    · intro x y
      simp only [LinearMap.smul_apply, hD x y, map_smul, smul_add]
    · intro g
      obtain ⟨b, hb⟩ := d g
      exact ⟨a * b, by simp only [LinearMap.smul_apply, hb, smul_smul]⟩

@[simp] theorem mem_derivationGrade {D : Module.End ℂ A} {γ : Charge} :
    D ∈ M.derivationGrade γ ↔ M.IsDerivation D ∧ M.HasDegree D γ := Iff.rfl

/-- A coordinate of a homogeneous operator on a specified basis vector. -/
def gradeCoefficient (γ g : Charge) : Module.End ℂ A →ₗ[ℂ] ℂ where
  toFun D := M.basis.coord (g + γ) (D (M.basis g))
  map_add' D E := by simp
  map_smul' a D := by simp

theorem derivationGrade_apply {D : Module.End ℂ A} {γ : Charge} (hD : D ∈ M.derivationGrade γ)
    (g : Charge) :
    D (M.basis g) = M.gradeCoefficient γ g D • M.basis (g + γ) := by
  obtain ⟨a, ha⟩ := (M.mem_derivationGrade.mp hD).2 g
  have hc : M.gradeCoefficient γ g D = a := by
    change M.basis.coord (g + γ) (D (M.basis g)) = a
    rw [ha, map_smul]
    simp
  rwa [hc]

theorem derivation_kills_unit {D : Module.End ℂ A} (hD : M.IsDerivation D) :
    D (M.basis 0) = 0 := by
  have h := hD (M.basis 0) (M.basis 0)
  rw [M.comm (D (M.basis 0)) (M.basis 0)] at h
  simp only [M.unit_left] at h
  linear_combination (norm := abel) -h

private theorem coefficient_eq_of_smul {g : Charge} {a b : ℂ}
    (h : a • M.basis g = b • M.basis g) : a = b := by
  exact (smul_left_injective ℂ (M.basis.ne_zero g)) h

/-- Every derivation of degree zero vanishes. -/
theorem derivationGrade_zero_eq_bot : M.derivationGrade 0 = ⊥ := by
  apply eq_bot_iff.mpr
  intro D hD
  rw [Submodule.mem_bot]
  apply M.basis.ext
  intro g
  change D (M.basis g) = 0
  obtain ⟨hd, hdeg⟩ := M.mem_derivationGrade.mp hD
  by_cases hg : g = 0
  · rw [hg]
    exact M.derivation_kills_unit hd
  obtain ⟨a, ha⟩ := hdeg g
  obtain ⟨b, hb⟩ := hdeg (-g)
  simp only [add_zero] at ha hb
  have hr := hd (M.basis g) (M.basis (-g))
  rw [M.opposite g hg, M.derivation_kills_unit hd, ha, hb, map_smul, LinearMap.smul_apply, map_smul,
    M.opposite g hg] at hr
  have hab : a + b = 0 := M.coefficient_eq_of_smul (g := 0) (by simpa only [add_smul, zero_smul] using hr.symm)
  have hsq := hd (M.basis g) (M.basis g)
  rw [M.square g hg, hb, ha, map_smul, LinearMap.smul_apply, map_smul, M.square g hg] at hsq
  have hb' : b = a + a := M.coefficient_eq_of_smul (g := -g) (by
    simpa only [add_smul] using hsq)
  have hzero : a = 0 := by linear_combination (1 / 3 : ℂ) * hab - (1 / 3 : ℂ) * hb'
  rw [ha, hzero, zero_smul]

/-- A derivation of degree `γ ≠ 0` annihilates both directions of its own projective point. -/
theorem derivationGrade_kills_directions {D : Module.End ℂ A} {γ : Charge}
    (hγ : γ ≠ 0) (hD : D ∈ M.derivationGrade γ) :
    D (M.basis γ) = 0 ∧ D (M.basis (-γ)) = 0 := by
  obtain ⟨hd, hdeg⟩ := M.mem_derivationGrade.mp hD
  obtain ⟨a, ha⟩ := hdeg γ
  obtain ⟨b, hb⟩ := hdeg (-γ)
  have hn : -γ ≠ 0 := neg_ne_zero.mpr hγ
  rw [charge_double_eq_neg] at ha
  rw [neg_add_cancel] at hb
  have hop := hd (M.basis γ) (M.basis (-γ))
  rw [M.opposite γ hγ, M.derivation_kills_unit hd, ha, hb, map_smul, LinearMap.smul_apply,
    map_smul, M.square (-γ) hn, neg_neg, M.comm (M.basis γ) (M.basis 0), M.unit_left] at hop
  have hab : a + b = 0 := M.coefficient_eq_of_smul (g := γ) (by
    simpa only [add_smul, zero_smul] using hop.symm)
  have hsq := hd (M.basis (-γ)) (M.basis (-γ))
  rw [M.square (-γ) hn, neg_neg, ha, hb, map_smul, LinearMap.smul_apply,
    map_smul, M.unit_left, M.comm (M.basis (-γ)) (M.basis 0), M.unit_left] at hsq
  have ha' : a = b + b := M.coefficient_eq_of_smul (g := -γ) (by
    simpa only [add_smul] using hsq)
  have hzero : b = 0 := by linear_combination (1 / 3 : ℂ) * hab - (1 / 3 : ℂ) * ha'
  have hzero' : a = 0 := by rw [ha', hzero, add_zero]
  rw [ha, hb, hzero, hzero', zero_smul, zero_smul]
  exact ⟨rfl, rfl⟩

/-- The commutator of two homogeneous derivations has the sum of their degrees. -/
theorem derivationGrade_bracket {D E : Module.End ℂ A} {γ δ : Charge}
    (hD : D ∈ M.derivationGrade γ) (hE : E ∈ M.derivationGrade δ) :
    operatorBracket D E ∈ M.derivationGrade (γ + δ) := by
  obtain ⟨hd, hdegD⟩ := M.mem_derivationGrade.mp hD
  obtain ⟨he, hdegE⟩ := M.mem_derivationGrade.mp hE
  refine M.mem_derivationGrade.mpr ⟨?_, ?_⟩
  · intro x y
    change D (E (M.product x y)) - E (D (M.product x y)) =
      M.product (D (E x) - E (D x)) y + M.product x (D (E y) - E (D y))
    rw [he x y, hd x y, map_add, map_add, hd (E x) y, hd x (E y),
      he (D x) y, he x (D y)]
    simp only [map_sub, LinearMap.sub_apply]
    abel
  · intro g
    obtain ⟨a, ha⟩ := hdegD g
    obtain ⟨b, hb⟩ := hdegE g
    obtain ⟨c, hc⟩ := hdegD (g + δ)
    obtain ⟨d, hd'⟩ := hdegE (g + γ)
    refine ⟨b * c - a * d, ?_⟩
    change D (E (M.basis g)) - E (D (M.basis g)) = _
    rw [ha, hb, map_smul, map_smul, hc, hd', smul_smul, smul_smul, sub_smul]
    rw [show g + δ + γ = g + (γ + δ) by abel, add_assoc g γ δ]

end NormalizedTernaryBasis

end
end ThirteenPlanes.Cartan
