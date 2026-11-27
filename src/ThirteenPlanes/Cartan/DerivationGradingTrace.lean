module

public import ThirteenPlanes.Cartan.DerivationGradingFixed

@[expose] public section

set_option backward.privateInPublic true

/-! Trace orthogonality and commutativity of opposite grade pairs. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

variable {A : Type*} [AddCommGroup A] [Module ℂ A]
variable (M : NormalizedTernaryBasis A)

/-- A nonzero shift of the character basis has zero operator trace. -/
theorem trace_eq_zero_of_nonzero_degree {γ : Charge} (hγ : γ ≠ 0) {D : Module.End ℂ A}
    (hd : M.HasDegree D γ) : LinearMap.trace ℂ A D = 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ M.basis, Matrix.trace]
  apply Finset.sum_eq_zero
  intro g _
  obtain ⟨c, hc⟩ := hd g
  have hne : g + γ ≠ g := fun h => hγ (add_left_cancel (show g + γ = g + 0 by simpa using h))
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hc, map_smul]
  simp [Basis.repr_self, hne]

/-- The trace of a product of homogeneous operators vanishes unless the degrees sum to zero. -/
theorem trace_mul_eq_zero_of_nonopposite {γ δ : Charge} (h : γ + δ ≠ 0)
    {D E : Module.End ℂ A} (hd : M.HasDegree D γ) (he : M.HasDegree E δ) :
    LinearMap.trace ℂ A (D * E) = 0 := by
  apply M.trace_eq_zero_of_nonzero_degree h
  intro g
  obtain ⟨e, hh⟩ := he g
  obtain ⟨d, hc⟩ := hd (g + δ)
  refine ⟨e * d, ?_⟩
  change D (E (M.basis g)) = _
  rw [hh, map_smul, hc, smul_smul, show g + δ + γ = g + (γ + δ) by abel]

private theorem trace_bracket_mul_left (X Y : Module.End ℂ A) :
    LinearMap.trace ℂ A (operatorBracket X Y * X) = 0 := by
  rw [operatorBracket, sub_mul, map_sub, sub_eq_zero]
  calc
    _ = LinearMap.trace ℂ A (X * X * Y) := LinearMap.trace_mul_cycle ℂ X Y X
    _ = LinearMap.trace ℂ A (Y * (X * X)) := LinearMap.trace_mul_comm ℂ (X * X) Y
    _ = _ := by rw [mul_assoc]

private theorem trace_bracket_mul_right (X Y : Module.End ℂ A) :
    LinearMap.trace ℂ A (operatorBracket X Y * Y) = 0 := by
  rw [operatorBracket, sub_mul, map_sub, sub_eq_zero]
  exact LinearMap.trace_mul_cycle ℂ X Y Y

variable [FiniteDimensional ℂ A]

private theorem trace_bracket_eq_zero_in_twoDim {γ : Charge}
    (hfin : Module.finrank ℂ (M.derivationGrade γ) = 2) (X Y Z : M.derivationGrade γ) :
    LinearMap.trace ℂ A (operatorBracket X.val Y.val * Z.val) = 0 := by
  let b := Module.finBasisOfFinrankEq ℂ (M.derivationGrade γ) hfin
  let U := (b 0).val
  let V := (b 1).val
  have hrep (T : M.derivationGrade γ) :
      T.val = b.repr T 0 • U + b.repr T 1 • V := by
    have h := b.sum_repr T
    rw [Fin.sum_univ_two] at h
    exact (congrArg Subtype.val h).symm
  have hbr : operatorBracket X.val Y.val =
      (b.repr X 0 * b.repr Y 1 - b.repr X 1 * b.repr Y 0) • operatorBracket U V := by
    rw [hrep X, hrep Y]
    simp only [operatorBracket, mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    module
  rw [hbr, hrep Z]
  simp only [smul_mul_assoc, mul_add, mul_smul_comm, map_smul, map_add,
    trace_bracket_mul_left, trace_bracket_mul_right, smul_zero, add_zero]

/-- The opposite-grade pairings supplied by the compact real form. -/
def OppositeTraceNondegenerate : Prop :=
  ∀ γ (D : Module.End ℂ A), D ∈ M.derivationGrade (-γ) → D ≠ 0 →
    ∃ E : Module.End ℂ A, E ∈ M.derivationGrade γ ∧ LinearMap.trace ℂ A (D * E) ≠ 0

private theorem derivationGrade_same_commutes (hRank : Module.finrank ℂ M.derivations = 52)
    (hTrace : M.OppositeTraceNondegenerate) {γ : Charge} (hγ : γ ≠ 0)
    {X Y : Module.End ℂ A} (hX : X ∈ M.derivationGrade γ) (hY : Y ∈ M.derivationGrade γ) :
    operatorBracket X Y = 0 := by
  by_contra hNe
  have hB := M.derivationGrade_bracket hX hY
  rw [charge_double_eq_neg] at hB
  obtain ⟨Z, hZ, hneq⟩ := hTrace γ (operatorBracket X Y) hB hNe
  exact hneq (M.trace_bracket_eq_zero_in_twoDim (M.derivationGrade_finrank_eq_two hRank hγ)
    ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩)

omit [FiniteDimensional ℂ A] in
private theorem derivationGrade_opposite_commutes {γ : Charge} {X Y : Module.End ℂ A}
    (hX : X ∈ M.derivationGrade γ) (hY : Y ∈ M.derivationGrade (-γ)) :
    operatorBracket X Y = 0 := by
  have h := M.derivationGrade_bracket hX hY
  rw [add_neg_cancel, M.derivationGrade_zero_eq_bot, Submodule.mem_bot] at h
  exact h

/-- Opposite grades form a commutative subalgebra under the compact trace pairing. -/
theorem gradePair_commutative (hRank : Module.finrank ℂ M.derivations = 52)
    (hTrace : M.OppositeTraceNondegenerate) {γ : Charge} (hγ : γ ≠ 0)
    {X Y : Module.End ℂ A} (hX : X ∈ M.gradePair γ) (hY : Y ∈ M.gradePair γ) :
    operatorBracket X Y = 0 := by
  obtain ⟨Xp, hXp, Xm, hXm, rfl⟩ := Submodule.mem_sup.mp hX
  obtain ⟨Yp, hYp, Ym, hYm, rfl⟩ := Submodule.mem_sup.mp hY
  have h₁ := M.derivationGrade_same_commutes hRank hTrace hγ hXp hYp
  have h₂ := M.derivationGrade_opposite_commutes hXp hYm
  have h₃ := M.derivationGrade_opposite_commutes hYp hXm
  have h₄ := M.derivationGrade_same_commutes hRank hTrace (neg_ne_zero.mpr hγ) hXm hYm
  simp only [operatorBracket, add_mul, mul_add] at h₁ h₂ h₃ h₄ ⊢
  linear_combination (norm := abel) h₁ + h₂ - h₃ + h₄

end
end ThirteenPlanes.Cartan.NormalizedTernaryBasis
