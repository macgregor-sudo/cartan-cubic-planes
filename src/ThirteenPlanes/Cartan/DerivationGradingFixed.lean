module

public import ThirteenPlanes.Cartan.DerivationGradingDimensions

@[expose] public section

set_option backward.privateInPublic true

/-! Fixed spaces and centralizers of opposite derivation grades. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
variable (M : NormalizedTernaryBasis A)

/-- The sum of the two character spaces defining the complexification of a Cartan summand. -/
def gradePair (γ : Charge) : Submodule ℂ (Module.End ℂ A) :=
  M.derivationGrade γ ⊔ M.derivationGrade (-γ)

theorem derivationGrade_le_gradePair (γ : Charge) :
    M.derivationGrade γ ≤ M.gradePair γ :=
  le_sup_left

theorem oppositeDerivationGrade_le_gradePair (γ : Charge) :
    M.derivationGrade (-γ) ≤ M.gradePair γ :=
  le_sup_right

theorem gradePair_neg (γ : Charge) : M.gradePair (-γ) = M.gradePair γ := by
  simp only [gradePair, neg_neg, sup_comm]

theorem gradePair_le_derivations (γ : Charge) : M.gradePair γ ≤ M.derivations := by
  rw [gradePair, sup_le_iff]
  constructor <;> intro D hD <;> exact (M.mem_derivationGrade.mp hD).1

theorem gradePair_finrank (hRank : Module.finrank ℂ M.derivations = 52)
    {γ : Charge} (hγ : γ ≠ 0) : Module.finrank ℂ (M.gradePair γ) = 4 := by
  have hne : γ ≠ -γ := by
    intro he
    have h := (charge_double_eq_neg γ).trans he.symm
    exact hγ (add_left_cancel (show γ + γ = γ + 0 by simpa using h))
  have hd : Disjoint (M.derivationGrade γ) (M.derivationGrade (-γ)) :=
    M.derivationGrades_independent.pairwiseDisjoint hne
  have h := Submodule.finrank_sup_add_finrank_inf_eq (M.derivationGrade γ) (M.derivationGrade (-γ))
  rw [hd.eq_bot, finrank_bot, add_zero, M.derivationGrade_finrank_eq_two hRank hγ,
    M.derivationGrade_finrank_eq_two hRank (neg_ne_zero.mpr hγ)] at h
  exact h

/-- The unital fixed subspace corresponding to the projective point of γ. -/
def gradeAxis (γ : Charge) : Submodule ℂ A :=
  Submodule.span ℂ {M.basis 0, M.basis γ, M.basis (-γ)}

theorem independentDirections_of_ne_axis {g h : Charge}
    (hg : g ≠ 0) (h0 : h ≠ 0) (h1 : h ≠ g) (hn : h ≠ -g) :
    IndependentDirections g h := by
  refine ⟨hg, fun a he => ?_⟩
  have hcases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 := by decide
  rcases hcases a with rfl | rfl | rfl
  · exact h0 (by simpa only [zero_smul] using he)
  · exact h1 (by simpa only [one_smul] using he)
  · exact hn (by simpa only [neg_smul, one_smul] using he)

omit [FiniteDimensional ℂ A] in
/-- A homogeneous derivation transports the specified input coefficient to
the shifted output coordinate and scales it by its basis coefficient. -/
theorem gradeCoefficient_action {D : Module.End ℂ A} {γ : Charge}
    (hD : D ∈ M.derivationGrade γ) (x : A) (g : Charge) :
    M.basis.coord (g + γ) (D x) = M.basis.coord g x * M.gradeCoefficient γ g D := by
  have he : (M.basis.coord (g + γ)).comp D = M.gradeCoefficient γ g D • M.basis.coord g := by
    apply M.basis.ext
    intro k
    change M.basis.coord (g + γ) (D (M.basis k)) =
      M.gradeCoefficient γ g D * M.basis.coord g (M.basis k)
    rw [M.derivationGrade_apply hD k, map_smul]
    by_cases hg : k = g
    · subst k
      simp [Basis.coord_apply, Basis.repr_self]
    · have hk : k + γ ≠ g + γ := fun h => hg (add_right_cancel h)
      simp [Basis.coord_apply, Basis.repr_self, hg, hk]
  have h := LinearMap.congr_fun he x
  exact h.trans (mul_comm _ _)

/-- Any direction independent of the derivation grade can be detected by
one homogeneous derivation with coefficient one on that direction. -/
theorem exists_gradeCoefficient_eq_one (hRank : Module.finrank ℂ M.derivations = 52)
    {γ g : Charge} (indep : IndependentDirections γ g) :
    ∃ D : Module.End ℂ A, D ∈ M.derivationGrade γ ∧ M.gradeCoefficient γ g D = 1 := by
  obtain ⟨B, hB₀, hB₁⟩ := exists_chargeBasis_extending_two indep
  obtain ⟨D, hD⟩ := (M.gradeEvaluation_bijective_of_rank hRank B hB₀).2 (1, 0)
  refine ⟨D.val, D.property, ?_⟩
  rw [← hB₁]
  exact congrArg Prod.fst hD

omit [FiniteDimensional ℂ A] in
theorem gradePair_kills_axes {γ : Charge} (hγ : γ ≠ 0) {D : Module.End ℂ A}
    (hD : D ∈ M.gradePair γ) :
    D (M.basis 0) = 0 ∧ D (M.basis γ) = 0 ∧ D (M.basis (-γ)) = 0 := by
  obtain ⟨X, hX, Y, hY, rfl⟩ := Submodule.mem_sup.mp hD
  have hX₀ := M.derivation_kills_unit (M.mem_derivationGrade.mp hX).1
  have hY₀ := M.derivation_kills_unit (M.mem_derivationGrade.mp hY).1
  obtain ⟨hX₁, hX₂⟩ := M.derivationGrade_kills_directions hγ hX
  obtain ⟨hY₂, hY₁⟩ := M.derivationGrade_kills_directions (neg_ne_zero.mpr hγ) hY
  rw [neg_neg] at hY₁
  simp only [LinearMap.add_apply, hX₀, hX₁, hX₂, hY₀, hY₁, hY₂, add_zero, and_self]

/-- The common complex kernel of the two opposite grades consists of the unit
and the two character directions that they share. -/
theorem mem_gradeAxis_iff_fixed (hRank : Module.finrank ℂ M.derivations = 52)
    {γ : Charge} (hγ : γ ≠ 0) (x : A) :
    x ∈ M.gradeAxis γ ↔ ∀ D ∈ M.gradePair γ, D x = 0 := by
  constructor
  · intro hx D hD
    obtain ⟨hu, hp, hn⟩ := M.gradePair_kills_axes hγ hD
    have hle : M.gradeAxis γ ≤ D.ker := by
      apply Submodule.span_le.mpr
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact hu
      · exact hp
      · exact hn
    exact hle hx
  · intro hFixed
    have hzero (g : Charge) (h0 : g ≠ 0) (h1 : g ≠ γ) (hn : g ≠ -γ) :
        M.basis.coord g x = 0 := by
      obtain ⟨D, hD, hCoeff⟩ := M.exists_gradeCoefficient_eq_one hRank
        (independentDirections_of_ne_axis hγ h0 h1 hn)
      have hAct := M.gradeCoefficient_action hD x g
      rw [hFixed D (M.derivationGrade_le_gradePair γ hD), map_zero, hCoeff, mul_one] at hAct
      exact hAct.symm
    rw [← M.basis.sum_repr x]
    apply Submodule.sum_mem
    intro g _
    by_cases h0 : g = 0
    · subst g
      exact (M.gradeAxis γ).smul_mem _ (Submodule.subset_span (by simp))
    by_cases h1 : g = γ
    · subst g
      exact (M.gradeAxis γ).smul_mem _ (Submodule.subset_span (by simp))
    by_cases hn : g = -γ
    · rw [hn]
      exact (M.gradeAxis γ).smul_mem _ (Submodule.subset_span (by simp))
    rw [← Basis.coord_apply, hzero g h0 h1 hn, zero_smul]
    exact Submodule.zero_mem _

private theorem derivationGrade_commuting_off_axis (hRank : Module.finrank ℂ M.derivations = 52)
    {γ α : Charge} (indep : IndependentDirections γ α)
    {D : Module.End ℂ A} (hD : D ∈ M.derivationGrade α)
    (hCom : ∀ E ∈ M.derivationGrade γ, operatorBracket D E = 0) :
    D = 0 := by
  have hγ := indep.left_ne_zero
  have hα := indep.right_ne_zero
  have hγa : D (M.basis γ) = 0 := by
    have hi : IndependentDirections γ (γ + α) := by
      refine ⟨hγ, fun b he => ?_⟩
      apply indep.right_not_multiple (b - 1)
      rw [sub_smul, one_smul, ← he]
      abel
    obtain ⟨E, hE, hCoeff⟩ := M.exists_gradeCoefficient_eq_one hRank hi
    have hEq := LinearMap.congr_fun (hCom E hE) (M.basis γ)
    change D (E (M.basis γ)) - E (D (M.basis γ)) = 0 at hEq
    rw [(M.derivationGrade_kills_directions hγ hE).1, map_zero, zero_sub, neg_eq_zero,
      M.derivationGrade_apply hD γ, map_smul, M.derivationGrade_apply hE (γ + α),
      hCoeff, one_smul] at hEq
    have hz := (smul_eq_zero.mp hEq).resolve_right (M.basis.ne_zero _)
    rw [M.derivationGrade_apply hD γ, hz, zero_smul]
  have hαa := (M.derivationGrade_kills_directions hα hD).1
  obtain ⟨B, hB₀, hB₁⟩ := exists_chargeBasis_extending_two indep
  let k := B 2
  obtain ⟨E, hE⟩ := (M.gradeEvaluation_bijective_of_rank hRank B hB₀).2 (1, 0)
  have hE₁ : M.gradeCoefficient γ α E.val = 1 := by
    rw [← hB₁]
    exact congrArg Prod.fst hE
  have hE₂ : M.gradeCoefficient γ k E.val = 0 := congrArg Prod.snd hE
  have hEα : E.val (M.basis α) = M.basis (α + γ) := by
    rw [M.derivationGrade_apply E.property, hE₁, one_smul]
  have hEk : E.val (M.basis k) = 0 := by
    rw [M.derivationGrade_apply E.property, hE₂, zero_smul]
  have hi : IndependentDirections (α + γ) k := by
    refine ⟨?_, fun t ht => ?_⟩
    · intro hz
      apply indep.right_not_multiple (-1)
      rw [neg_smul, one_smul]
      exact eq_neg_of_add_eq_zero_left hz
    · have h := congrArg (B.coord 2) ht
      simp [k, ← hB₁, ← hB₀, Basis.coord_apply, Basis.repr_self] at h
  have hnonzero : E.val (M.basis (α + k)) ≠ 0 := by
    intro hz
    obtain ⟨c, hc⟩ := M.homogeneous_product α k
    have he := (M.mem_derivationGrade.mp E.property).1 (M.basis α) (M.basis k)
    rw [hc, map_smul, hz, smul_zero, hEα, hEk, map_zero, add_zero] at he
    exact M.independent_product _ _ hi.left_ne_zero hi.right_ne_zero
      hi.right_ne_left hi.right_ne_neg_left he.symm
  have hDk : D (M.basis k) = 0 := by
    have he := LinearMap.congr_fun (hCom E.val E.property) (M.basis k)
    change D (E.val (M.basis k)) - E.val (D (M.basis k)) = 0 at he
    rw [hEk, map_zero, zero_sub, neg_eq_zero, M.derivationGrade_apply hD k,
      map_smul, add_comm k α] at he
    have hh := (smul_eq_zero.mp he).resolve_right hnonzero
    rw [M.derivationGrade_apply hD k, hh, zero_smul]
  have hker := M.generated_basis_eq_top B
    (M.derivation_ker_productClosed (M.mem_derivationGrade.mp hD).1)
    (M.derivation_kills_unit (M.mem_derivationGrade.mp hD).1) (by
      intro i
      change D (M.basis (B i)) = 0
      fin_cases i
      · exact hB₀.symm ▸ hγa
      · exact hB₁.symm ▸ hαa
      · exact hDk)
  exact LinearMap.ker_eq_top.mp hker

omit [FiniteDimensional ℂ A] in
private theorem degreeProjection_bracket_right {D E : Module.End ℂ A} {α γ : Charge}
    (hD : M.IsDerivation D) (hE : E ∈ M.derivationGrade γ) :
    M.degreeProjection (α + γ) (operatorBracket D E) =
      operatorBracket (M.degreeProjection α D) E := by
  classical
  have hsum : operatorBracket D E = ∑ β, operatorBracket (M.degreeProjection β D) E := by
    conv_lhs => rw [← M.sum_degreeProjection D]
    simp only [operatorBracket, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  change (M.degreeProjectionLinear (α + γ)) (∑ β, operatorBracket (M.degreeProjection β D) E) = _
  rw [map_sum, Finset.sum_eq_single α]
  · change M.degreeProjection (α + γ) (operatorBracket (M.degreeProjection α D) E) = _
    rw [M.degreeProjection_of_mem_derivationGrade
      (M.derivationGrade_bracket (M.degreeProjection_mem_derivationGrade hD α) hE), ite_eq_left rfl]
  · intro β _ hβα
    change M.degreeProjection (α + γ) (operatorBracket (M.degreeProjection β D) E) = _
    have hn : α + γ ≠ β + γ := fun h => hβα (add_right_cancel h).symm
    rw [M.degreeProjection_of_mem_derivationGrade
      (M.derivationGrade_bracket (M.degreeProjection_mem_derivationGrade hD β) hE), ite_eq_right hn]
  · simp

/-- A derivation centralizing the two opposite grades lies in their sum. -/
theorem mem_gradePair_of_centralizes (hRank : Module.finrank ℂ M.derivations = 52)
    {γ : Charge} (hγ : γ ≠ 0) {D : Module.End ℂ A} (hD : D ∈ M.derivations)
    (hCom : ∀ E ∈ M.gradePair γ, operatorBracket D E = 0) :
    D ∈ M.gradePair γ := by
  have hzero (α : Charge) (h₁ : α ≠ γ) (h₂ : α ≠ -γ) :
      M.degreeProjection α D = 0 := by
    have hp := M.degreeProjection_mem_derivationGrade (M.mem_derivations.mp hD) α
    by_cases ha : α = 0
    · subst α
      rw [M.derivationGrade_zero_eq_bot, Submodule.mem_bot] at hp
      exact hp
    apply M.derivationGrade_commuting_off_axis hRank
      (independentDirections_of_ne_axis hγ ha h₁ h₂) hp
    intro E hE
    rw [← M.degreeProjection_bracket_right (M.mem_derivations.mp hD) hE,
      hCom E (M.derivationGrade_le_gradePair γ hE)]
    exact (M.degreeProjectionLinear _).map_zero
  rw [← M.sum_degreeProjection D]
  apply Submodule.sum_mem
  intro α _
  by_cases h₁ : α = γ
  · subst α
    exact M.derivationGrade_le_gradePair γ (M.degreeProjection_mem_derivationGrade (M.mem_derivations.mp hD) γ)
  by_cases h₂ : α = -γ
  · rw [h₂]
    exact M.oppositeDerivationGrade_le_gradePair γ (M.degreeProjection_mem_derivationGrade (M.mem_derivations.mp hD) (-γ))
  rw [hzero α h₁ h₂]
  exact Submodule.zero_mem _

end
end ThirteenPlanes.Cartan.NormalizedTernaryBasis
