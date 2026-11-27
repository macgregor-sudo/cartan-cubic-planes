module

public import ThirteenPlanes.Cartan.GradedLineRestrictionProjection
public import ThirteenPlanes.Cartan.DerivationGradingDimensions

@[expose] public section

set_option backward.privateInPublic true

/-! Every derivation of the graded line lifts to the sum of its ambient grades. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

variable {A : Type*} [AddCommGroup A] [Module ℂ A] (M : NormalizedTernaryBasis A)
variable (L : Submodule (ZMod 3) Charge)

local instance : Fintype L := Fintype.ofFinite L

local notation "Q" => M.gradedLineSubspace L
local notation "b" => M.gradedLineBasis L
local notation "μ" => M.gradedLineProduct L

private theorem lineProduct_comm (x y : Q) : μ x y = μ y x :=
  Subtype.ext (M.comm _ _)

private theorem lineProduct_square (g : L) (hg : g ≠ 0) : μ (b g) (b g) = b (-g) := by
  apply Subtype.ext
  simp only [M.gradedLineProduct_coe, M.gradedLineBasis_coe, Submodule.coe_neg]
  exact M.square g.val (fun he => hg (Subtype.ext he))

private theorem lineProduct_opposite (g : L) (hg : g ≠ 0) : μ (b g) (b (-g)) = b 0 := by
  apply Subtype.ext
  simp only [M.gradedLineProduct_coe, M.gradedLineBasis_coe, Submodule.coe_neg, Submodule.coe_zero]
  exact M.opposite g.val (fun he => hg (Subtype.ext he))

theorem gradedLineDerivation_kills_unit {D : Module.End ℂ Q} (hD : D ∈ M.gradedLineDerivations L) :
    D (b 0) = 0 := by
  have eq := (M.mem_gradedLineDerivations L).mp hD (b 0) (b 0)
  rw [M.lineProduct_comm L (D (b 0)) (b 0)] at eq
  simp only [M.gradedLineBasis_unit_left] at eq
  linear_combination (norm := abel) -eq

private theorem lineCoefficient_eq_of_smul {g : L} {a c : ℂ} (eq : a • b g = c • b g) :
    a = c :=
  (smul_left_injective ℂ ((b).ne_zero g)) eq

theorem gradedLineDegree_zero {D : Module.End ℂ Q} (hD : D ∈ M.gradedLineDerivations L)
    (hDegree : M.HasLineDegree L D 0) : D = 0 := by
  apply (b).ext
  intro g
  change D (b g) = 0
  by_cases hg : g = 0
  · rw [hg]
    exact M.gradedLineDerivation_kills_unit L hD
  obtain ⟨c, hc⟩ := hDegree g
  obtain ⟨d, hd⟩ := hDegree (-g)
  simp only [add_zero] at hc hd
  have hp := (M.mem_gradedLineDerivations L).mp hD (b g) (b (-g))
  rw [M.lineProduct_opposite L g hg, M.gradedLineDerivation_kills_unit L hD, hc, hd,
    map_smul, LinearMap.smul_apply, map_smul, M.lineProduct_opposite L g hg] at hp
  have e₁ : c + d = 0 := M.lineCoefficient_eq_of_smul L (g := 0)
    (by simpa only [add_smul, zero_smul] using hp.symm)
  have hsq := (M.mem_gradedLineDerivations L).mp hD (b g) (b g)
  rw [M.lineProduct_square L g hg, hd, hc, map_smul, LinearMap.smul_apply, map_smul,
    M.lineProduct_square L g hg] at hsq
  have e₂ : d = c + c := M.lineCoefficient_eq_of_smul L (g := -g)
    (by simpa only [add_smul] using hsq)
  have hz : c = 0 := by linear_combination (1 / 3 : ℂ) * e₁ - (1 / 3 : ℂ) * e₂
  rw [hc, hz, zero_smul]

theorem gradedLineDegree_kills_self {D : Module.End ℂ Q} {γ : L} (hγ : γ ≠ 0)
    (hD : D ∈ M.gradedLineDerivations L) (hDegree : M.HasLineDegree L D γ) :
    D (b γ) = 0 := by
  obtain ⟨a, ha⟩ := hDegree γ
  obtain ⟨c, hc⟩ := hDegree (-γ)
  have two : γ + γ = -γ := Subtype.ext (charge_double_eq_neg γ.val)
  rw [two] at ha
  rw [neg_add_cancel] at hc
  have hn : -γ ≠ 0 := neg_ne_zero.mpr hγ
  have hop := (M.mem_gradedLineDerivations L).mp hD (b γ) (b (-γ))
  rw [M.lineProduct_opposite L γ hγ, M.gradedLineDerivation_kills_unit L hD,
    ha, hc, map_smul, LinearMap.smul_apply, map_smul, M.lineProduct_square L (-γ) hn,
    neg_neg, M.lineProduct_comm L (b γ) (b 0), M.gradedLineBasis_unit_left] at hop
  have e₁ : a + c = 0 := M.lineCoefficient_eq_of_smul L (g := γ)
    (by simpa only [add_smul, zero_smul] using hop.symm)
  have hsq := (M.mem_gradedLineDerivations L).mp hD (b (-γ)) (b (-γ))
  rw [M.lineProduct_square L (-γ) hn, neg_neg, ha, hc, map_smul, LinearMap.smul_apply, map_smul,
    M.gradedLineBasis_unit_left, M.lineProduct_comm L (b (-γ)) (b 0), M.gradedLineBasis_unit_left] at hsq
  have e₂ : a = c + c := M.lineCoefficient_eq_of_smul L (g := -γ)
    (by simpa only [add_smul] using hsq)
  have hz : a = 0 := by linear_combination (2 / 3 : ℂ) * e₁ + (1 / 3 : ℂ) * e₂
  rw [ha, hz, zero_smul]

theorem gradedLine_exists_basis (hdim : Module.finrank (ZMod 3) L = 2)
    {γ : L} (hγ : γ ≠ 0) :
    ∃ B : Basis (Fin 2) (ZMod 3) L, B 0 = γ ∧ IndependentDirections γ.val (B 1).val := by
  have hc : 1 < Module.finrank (ZMod 3) L := by omega
  obtain ⟨z, hz⟩ := exists_linearIndependent_pair_of_one_lt_finrank hc hγ
  have hs := hz.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])
  let B := Basis.mk hz (by rw [hs])
  have hB₀ : B 0 = γ := by rw [Basis.mk_apply]; rfl
  have hB₁ : B 1 = z := by rw [Basis.mk_apply]; rfl
  refine ⟨B, hB₀, ⟨fun e => hγ (Subtype.ext e), fun c e => ?_⟩⟩
  have he : B 1 = c • B 0 := Subtype.ext (by rw [hB₀]; exact e)
  have hcoord := congrArg (B.coord 1) he
  simp [Basis.coord_apply, Basis.repr_self] at hcoord

theorem gradedLineDerivation_eq_of_basis {γ : L} (B : Basis (Fin 2) (ZMod 3) L)
    (hB : B 0 = γ) (hindep : IndependentDirections γ.val (B 1).val)
    {D E : Module.End ℂ Q} (hD : D ∈ M.gradedLineDerivations L) (hE : E ∈ M.gradedLineDerivations L)
    (atγ : D (b γ) = E (b γ)) (atmate : D (b (B 1)) = E (b (B 1))) : D = E := by
  let T := D - E
  let K := T.ker.map (Q).subtype
  have ht : T ∈ M.gradedLineDerivations L := (M.gradedLineDerivations L).sub_mem hD hE
  have hcl : M.ProductClosed K := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨μ x y, ?_, rfl⟩
    change T x = 0 at hx
    change T y = 0 at hy
    change T (μ x y) = 0
    rw [(M.mem_gradedLineDerivations L).mp ht, hx, hy]
    simp
  have unit : M.basis 0 ∈ K := ⟨b 0, M.gradedLineDerivation_kills_unit L ht, by simp⟩
  have first : M.basis γ.val ∈ K :=
    ⟨b γ, by change D (b γ) - E (b γ) = 0; rw [atγ, sub_self], by simp⟩
  have second : M.basis (B 1).val ∈ K :=
    ⟨b (B 1), by change D (b (B 1)) - E (b (B 1)) = 0; rw [atmate, sub_self], by simp⟩
  apply (b).ext
  intro t
  have hsum := B.sum_repr t
  rw [Fin.sum_univ_two, hB] at hsum
  have expanded : t.val = B.coord 0 t • γ.val + B.coord 1 t • (B 1).val :=
    (congrArg Subtype.val hsum).symm
  have hmem : M.basis t.val ∈ K := by
    rw [expanded]
    exact M.generated_line_basis_mem hcl unit hindep first second _ _
  obtain ⟨x, hx, he⟩ := hmem
  have hh : x = b t := Subtype.ext (by simpa only [Submodule.subtype_apply, M.gradedLineBasis_coe] using he)
  change T x = 0 at hx
  rw [hh] at hx
  exact sub_eq_zero.mp hx

/-- Restriction of an ambient homogeneous derivation has the same degree on the line. -/
theorem gradedLineRestriction_hasDegree {D : Module.End ℂ A} {γ : L}
    (hD : D ∈ M.derivationGrade γ.val) :
    M.HasLineDegree L (M.gradedLineRestriction L ⟨D, Submodule.mem_iSup_of_mem γ hD⟩).val γ := by
  intro g
  have h := M.derivationGrade_apply hD g.val
  refine ⟨M.gradeCoefficient γ.val g.val D, Subtype.ext ?_⟩
  simpa only [M.gradedLineRestriction_apply, M.gradedLineBasis_coe, Submodule.coe_smul, Submodule.coe_add] using h

variable [FiniteDimensional ℂ A]

private theorem gradedLine_homogeneous_lift (hdim : Module.finrank (ZMod 3) L = 2)
    (ranks : ∀ γ : Charge, γ ≠ 0 → Module.finrank ℂ (M.derivationGrade γ) = 2)
    {D : Module.End ℂ Q} (hD : D ∈ M.gradedLineDerivations L) {γ : L} (hDegree : M.HasLineDegree L D γ) :
    ∃ E : M.lineDerivations L, (M.gradedLineRestriction L E).val = D := by
  by_cases hγ : γ = 0
  · subst γ
    refine ⟨0, ?_⟩
    rw [M.gradedLineDegree_zero L hD hDegree, map_zero]
    rfl
  obtain ⟨B, hB, indep⟩ := gradedLine_exists_basis L hdim hγ
  obtain ⟨C, hC₀, hC₁⟩ := exists_chargeBasis_extending_two indep
  obtain ⟨c, hc⟩ := hDegree (B 1)
  obtain ⟨u, hu⟩ := (M.gradeEvaluation_bijective C hC₀ (ranks _ indep.left_ne_zero)).surjective (c, 0)
  have hcoef := congrArg Prod.fst hu
  change M.gradeCoefficient γ.val (C 1) u.val = c at hcoef
  rw [hC₁] at hcoef
  let E : M.lineDerivations L := ⟨u, Submodule.mem_iSup_of_mem γ u.property⟩
  let V := M.gradedLineRestriction L E
  have vdeg : M.HasLineDegree L V.val γ := M.gradedLineRestriction_hasDegree L u.property
  refine ⟨E, M.gradedLineDerivation_eq_of_basis L B hB indep V.property hD ?_ ?_⟩
  · rw [M.gradedLineDegree_kills_self L hγ V.property vdeg, M.gradedLineDegree_kills_self L hγ hD hDegree]
  · apply Subtype.ext
    simp only [hc, Submodule.coe_smul, M.gradedLineRestriction_apply, M.gradedLineBasis_coe, Submodule.coe_add]
    change u.val (M.basis (B 1).val) = c • M.basis ((B 1).val + γ.val)
    rw [M.derivationGrade_apply u.property, hcoef]

/-- The actual complex restriction to a projective line is onto all derivations of that line. -/
theorem gradedLineRestriction_surjective (hdim : Module.finrank (ZMod 3) L = 2)
    (ranks : ∀ γ : Charge, γ ≠ 0 → Module.finrank ℂ (M.derivationGrade γ) = 2) :
    Function.Surjective (M.gradedLineRestriction L) := by
  classical
  intro D
  have hasLift (γ : L) : ∃ E : M.lineDerivations L, (M.gradedLineRestriction L E).val =
      M.gradedLineDegreeProjection L γ D.val :=
    M.gradedLine_homogeneous_lift L hdim ranks (M.gradedLineDegreeProjection_derivation L γ D.property)
      (M.gradedLineDegreeProjection_hasDegree L γ D.val)
  choose E hE using hasLift
  refine ⟨∑ γ : L, E γ, ?_⟩
  rw [map_sum]
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [hE, M.gradedLineDegreeProjection_sum]

end

end ThirteenPlanes.Cartan.NormalizedTernaryBasis
