module

public import ThirteenPlanes.Cartan.DerivationGradingGeneration
public import ThirteenPlanes.Cartan.DerivationGradingProjection
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! The nonzero homogeneous derivation grades of a rank-52 ternary grading have dimension two. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

theorem charge_finrank : Module.finrank (ZMod 3) Charge = 3 := by
  change Module.finrank (ZMod 3) (Fin 3 → ZMod 3) = 3
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- Extend any two independent ternary directions to a charge basis in the given order. -/
theorem exists_chargeBasis_extending_two {g h : Charge} (indep : IndependentDirections g h) :
    ∃ B : Basis (Fin 3) (ZMod 3) Charge, B 0 = g ∧ B 1 = h := by
  let v : Fin 2 → Charge := ![g, h]
  have hv : LinearIndependent (ZMod 3) v :=
    (LinearIndependent.pair_iff' indep.left_ne_zero).mpr (fun a hz => indep.right_not_multiple a hz.symm)
  let S := Submodule.span (ZMod 3) (Set.range v)
  have hne : S ≠ ⊤ := by
    intro hS
    have hdim : Module.finrank (ZMod 3) S = 2 :=
      (finrank_span_eq_card hv).trans (Fintype.card_fin 2)
    rw [hS, finrank_top, charge_finrank] at hdim
    omega
  obtain ⟨k, hk⟩ : ∃ k : Charge, k ∉ S := by
    by_contra! hn
    apply hne
    exact eq_top_iff.mpr (fun k _ => hn k)
  let w : Fin 3 → Charge := Fin.snoc v k
  have hw : LinearIndependent (ZMod 3) w := hv.finSnoc hk
  have hs : Submodule.span (ZMod 3) (Set.range w) = ⊤ :=
    hw.span_eq_top_of_card_eq_finrank (by rw [charge_finrank, Fintype.card_fin])
  let B := Basis.mk hw (by rw [hs])
  refine ⟨B, ?_, ?_⟩
  · change B 0 = g
    rw [Basis.mk_apply]
    rfl
  · change B 1 = h
    rw [Basis.mk_apply]
    rfl

/-- Every nonzero direction can be the first vector of a charge basis. -/
theorem exists_chargeBasis_starting_at {g : Charge} (hg : g ≠ 0) :
    ∃ B : Basis (Fin 3) (ZMod 3) Charge, B 0 = g := by
  let S := Submodule.span (ZMod 3) {g}
  have hne : S ≠ ⊤ := by
    intro hS
    have hdim : Module.finrank (ZMod 3) S = 1 := finrank_span_singleton hg
    rw [hS, finrank_top, charge_finrank] at hdim
    omega
  obtain ⟨h, hh⟩ : ∃ h : Charge, h ∉ S := by
    by_contra! hn
    apply hne
    exact eq_top_iff.mpr (fun h _ => hn h)
  have indep : IndependentDirections g h := by
    refine ⟨hg, fun a e => ?_⟩
    apply hh
    rw [e]
    exact S.smul_mem a (Submodule.subset_span (Set.mem_singleton g))
  obtain ⟨B, hB, _⟩ := exists_chargeBasis_extending_two indep
  exact ⟨B, hB⟩

variable {A : Type*} [AddCommGroup A] [Module ℂ A]
variable (M : NormalizedTernaryBasis A)

theorem derivationGrade_finrank_le_two (γ : Charge) (hγ : γ ≠ 0) :
    Module.finrank ℂ (M.derivationGrade γ) ≤ 2 := by
  obtain ⟨B, hB⟩ := exists_chargeBasis_starting_at hγ
  have h := LinearMap.finrank_le_finrank_of_injective (M.gradeEvaluation_injective B hB)
  rwa [Module.finrank_prod, Module.finrank_self] at h

variable [FiniteDimensional ℂ A]

theorem derivationGrades_finrank_sum :
    Module.finrank ℂ M.derivations = ∑ γ, Module.finrank ℂ (M.derivationGrade γ) := by
  rw [← M.derivationGrades_iSup_eq, Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj M.derivationGrades_independent.dfinsupp_lsum_injective]
  change Module.finrank ℂ (DirectSum Charge fun g => ↥(M.derivationGrade g)) = _
  rw [Module.finrank_directSum]

/-- The total rank 52 forces two complex dimensions in each of the 26 nonzero grades. -/
theorem derivationGrade_finrank_eq_two (hRank : Module.finrank ℂ M.derivations = 52)
    {γ : Charge} (hγ : γ ≠ 0) :
    Module.finrank ℂ (M.derivationGrade γ) = 2 := by
  classical
  let d := fun g : Charge => Module.finrank ℂ (M.derivationGrade g)
  let b := fun g : Charge => if g = 0 then 0 else 2
  have hb : ∑ g, b g = 52 := by
    rw [← Finset.sum_erase_add Finset.univ b (Finset.mem_univ 0)]
    have hErase : ∑ g ∈ (Finset.univ : Finset Charge).erase 0, b g =
        ∑ _g ∈ (Finset.univ : Finset Charge).erase 0, 2 := by
      apply Finset.sum_congr rfl
      intro g hg
      simp only [b, ite_eq_right (Finset.ne_of_mem_erase hg)]
    rw [hErase, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have hc : Fintype.card Charge = 27 := by decide
    rw [hc]
    rfl
  have hd : ∑ g, d g = 52 := M.derivationGrades_finrank_sum.symm.trans hRank
  have hle (g : Charge) : d g ≤ b g := by
    by_cases hz : g = 0
    · subst g
      change Module.finrank ℂ (M.derivationGrade 0) ≤ b 0
      rw [M.derivationGrade_zero_eq_bot, finrank_bot]
      exact Nat.zero_le _
    · simpa only [b, ite_eq_right hz] using M.derivationGrade_finrank_le_two g hz
  have heq : d γ = b γ := by
    by_contra hneq
    have hlt := Finset.sum_lt_sum (s := (Finset.univ : Finset Charge))
      (fun i _ => hle i) ⟨γ, Finset.mem_univ γ, lt_of_le_of_ne (hle γ) hneq⟩
    rw [hb, hd] at hlt
    exact (lt_irrefl _ hlt)
  simpa only [b, ite_eq_right hγ] using heq

/-- For every charge basis starting at a nonzero grade, the two coefficients
parametrize the homogeneous derivation space. -/
theorem gradeEvaluation_bijective_of_rank
    (hRank : Module.finrank ℂ M.derivations = 52)
    {γ : Charge} (B : Basis (Fin 3) (ZMod 3) Charge) (hB : B 0 = γ) :
    Function.Bijective (M.gradeEvaluation γ B) :=
  M.gradeEvaluation_bijective B hB (M.derivationGrade_finrank_eq_two hRank (hB ▸ B.ne_zero 0))

end
end ThirteenPlanes.Cartan.NormalizedTernaryBasis
