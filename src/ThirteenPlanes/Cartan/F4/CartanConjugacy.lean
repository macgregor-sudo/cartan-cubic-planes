/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.F4.AutomorphismCompact
public import ThirteenPlanes.Cartan.CompactCartanRegular
public import ThirteenPlanes.Cartan.GradedLieNormalizerAlbert
public import ThirteenPlanes.Cartan.GradeRealAlbertOD
public import ThirteenPlanes.Cartan.GradedActionWitness
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

set_option backward.privateInPublic true

/-! Ordinary compact Albert Cartans are conjugate by actual Jordan automorphisms. -/

namespace ThirteenPlanes.Cartan

open NormedSpace

noncomputable section

section Differentiation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

local instance nativeF4DifferentiationNormedRing : NormedRing (V →L[ℝ] V) := ContinuousLinearMap.toNormedRing
local instance nativeF4DifferentiationTopologicalRing : IsTopologicalRing (V →L[ℝ] V) := NonUnitalSeminormedRing.toIsTopologicalRing
local instance nativeF4DifferentiationRationalAlgebra : NormedAlgebra ℚ (V →L[ℝ] V) := NormedAlgebra.restrictScalars ℚ ℝ _

omit [CompleteSpace V] in
private theorem exp_zero_smul (Z : V →L[ℝ] V) : exp ((0 : ℝ) • Z) = 1 := by
  rw [zero_smul, exp_zero]

omit [CompleteSpace V] in
private theorem exp_neg_zero_smul (Z : V →L[ℝ] V) : exp (-((0 : ℝ) • Z)) = 1 := by
  rw [zero_smul, neg_zero, exp_zero]

private theorem hasDerivAt_trace_conjugation (L : (V →L[ℝ] V) →L[ℝ] ℝ) (Z D Y : V →L[ℝ] V) :
    HasDerivAt (fun t : ℝ => -L (exp (t • Z) * D * exp (-(t • Z)) * Y))
      (-L ((Z * D - D * Z) * Y)) 0 := by
  have h₁ := hasDerivAt_exp_smul_const Z (0 : ℝ)
  rw [zero_smul, exp_zero, one_mul] at h₁
  have h₂ : HasDerivAt (fun t : ℝ => exp (-(t • Z))) (-Z) 0 := by
    have hn := hasDerivAt_exp_smul_const (-Z) (0 : ℝ)
    rw [zero_smul, exp_zero, one_mul] at hn
    simpa only [smul_neg] using hn
  have h := (((h₁.mul_const D).mul h₂).mul_const Y)
  have hc := (-L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simpa only [Function.comp_def, Pi.mul_apply, neg_apply, exp_zero_smul,
    exp_neg_zero_smul, one_mul, mul_one, mul_neg, sub_eq_add_neg, add_comm] using hc

end Differentiation

attribute [local instance 100] LieRing.ofAssociativeRing

local instance nativeF4AlbertCompleteSpace : CompleteSpace Glennie.Albert := FiniteDimensional.completeSpace ℝ Glennie.Albert
local instance nativeF4AlbertEndNormedRing : NormedRing AlbertContinuousEnd := ContinuousLinearMap.toNormedRing
local instance nativeF4AlbertEndTopologicalRing : IsTopologicalRing AlbertContinuousEnd :=
  NonUnitalSeminormedRing.toIsTopologicalRing
local instance nativeF4AlbertEndRationalAlgebra : NormedAlgebra ℚ AlbertContinuousEnd := NormedAlgebra.restrictScalars ℚ ℝ _

private def derivationExponential (Z : NativeAlbertDerivations) (t : ℝ) : Glennie.CompactAutomorphism :=
  albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv (t • Z))

private theorem derivationCLM_lie (Z D : NativeAlbertDerivations) :
    nativeAlbertDerivationCLM ⁅Z, D⁆ =
      nativeAlbertDerivationCLM Z * nativeAlbertDerivationCLM D -
        nativeAlbertDerivationCLM D * nativeAlbertDerivationCLM Z := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

private theorem tracePairing_clm (D Y : NativeAlbertDerivations) :
    nativeAlbertTracePairing D Y =
      -albertOperatorTrace (nativeAlbertDerivationCLM D * nativeAlbertDerivationCLM Y) := rfl

private theorem nativeAlbertLieAction_comp (g h : Glennie.CompactAutomorphism)
    (D : NativeAlbertDerivations) :
    nativeAlbertLieAction (g.comp h) D = nativeAlbertLieAction g (nativeAlbertLieAction h D) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

private theorem exp_conjugation_clm (Z D : NativeAlbertDerivations) (t : ℝ) :
    nativeAlbertDerivationCLM (nativeAlbertLieAction (derivationExponential Z t) D) =
      exp (t • nativeAlbertDerivationCLM Z) * nativeAlbertDerivationCLM D *
        exp (-(t • nativeAlbertDerivationCLM Z)) := by
  apply ContinuousLinearMap.ext
  intro x
  change ((albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv (t • Z))).equiv.conj D.val) x = _
  rw [albertExpCompactAutomorphism_conjugate_apply]
  have h : LinearMap.toContinuousLinearMap (nativeAlbertDerivationSkewEquiv (t • Z)).val.val =
      t • nativeAlbertDerivationCLM Z := rfl
  rw [h]
  rfl

private theorem derivationExponential_zero (Z D : NativeAlbertDerivations) :
    nativeAlbertLieAction (derivationExponential Z 0) D = D := by
  apply Subtype.ext
  apply (LinearMap.toContinuousLinearMap : Module.End ℝ Glennie.Albert ≃ₗ[ℝ]
    AlbertContinuousEnd).injective
  change nativeAlbertDerivationCLM (nativeAlbertLieAction (derivationExponential Z 0) D) =
    nativeAlbertDerivationCLM D
  rw [exp_conjugation_clm, exp_zero_smul, exp_neg_zero_smul, one_mul, mul_one]

private theorem hasDerivAt_nativePairing (Z D Y : NativeAlbertDerivations) :
    HasDerivAt (fun t : ℝ => nativeAlbertTracePairing (nativeAlbertLieAction (derivationExponential Z t) D) Y)
      (nativeAlbertTracePairing ⁅Z, D⁆ Y) 0 := by
  simp only [tracePairing_clm, exp_conjugation_clm, derivationCLM_lie]
  exact hasDerivAt_trace_conjugation albertOperatorTrace _ _ _

/-- An actual native Jordan automorphism moves a chosen Albert derivation so that it
commutes with another chosen derivation. -/
theorem exists_nativeAlbertLieAction_commutes (X Y : NativeAlbertDerivations) :
    ∃ g : Glennie.CompactAutomorphism, ⁅nativeAlbertLieAction g X, Y⁆ = 0 := by
  obtain ⟨g, hmax⟩ := exists_nativeAlbertTracePairing_maximum X Y
  let D := nativeAlbertLieAction g X
  have hzero (Z : NativeAlbertDerivations) : nativeAlbertTracePairing ⁅Z, D⁆ Y = 0 := by
    have hlocal : IsLocalMax (fun t : ℝ =>
        nativeAlbertTracePairing (nativeAlbertLieAction (derivationExponential Z t) D) Y) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      have hm := hmax ((derivationExponential Z t).comp g)
      rw [nativeAlbertLieAction_comp] at hm
      change nativeAlbertTracePairing (nativeAlbertLieAction (derivationExponential Z t) D) Y ≤
        nativeAlbertTracePairing (nativeAlbertLieAction (derivationExponential Z 0) D) Y
      rw [derivationExponential_zero]
      exact hm
    exact hlocal.hasDerivAt_eq_zero (hasDerivAt_nativePairing Z D Y)
  refine ⟨g, nativeAlbertTracePairing_definite _ ?_⟩
  rw [← nativeAlbertTracePairing_invariant]
  exact hzero ⁅D, Y⁆

/-- Any two ordinary compact Albert Cartans are conjugate by an actual real Jordan automorphism. -/
/- This proves the native compact Albert case of Cartan conjugacy, cited in the paper
from Anthony Knapp (1997, Theorem 3.6, p. 16). The proof uses regular centralizers
and maximizes an invariant pairing over actual Albert automorphisms. -/
theorem nativeAlbertCartans_conjugate (T U : LieSubalgebra ℝ NativeAlbertDerivations)
    (hT : T.IsCartanSubalgebra) (hU : U.IsCartanSubalgebra) :
    ∃ g : Glennie.CompactAutomorphism, T.map (nativeAlbertLieAction g).toLieHom = U := by
  have hK := nativeAlbert_compactKilling_of_grading nativeGradingHom_isTernaryGrading
  have hcT := (compactCartan_iff_cartan hK T).mpr hT
  have hcU := (compactCartan_iff_cartan hK U).mpr hU
  obtain ⟨x, _, regularT⟩ := compactCartan_exists_centralizer hK T hcT
  obtain ⟨y, _, regularU⟩ := compactCartan_exists_centralizer hK U hcU
  obtain ⟨g, hxy⟩ := exists_nativeAlbertLieAction_commutes x y
  let f := nativeAlbertLieAction g
  have hxU : f x ∈ U := (regularU (f x)).mp (by rw [← lie_skew y (f x), hxy, neg_zero])
  have hUle : U ≤ T.map f.toLieHom := by
    intro z hz
    have hc := (hcU (f x)).2 hxU z hz
    obtain ⟨w, rfl⟩ := f.surjective z
    refine ⟨w, (regularT w).mp (f.injective ?_), rfl⟩
    change f ⁅x, w⁆ = f 0
    change ⁅f x, f w⁆ = 0 at hc
    rw [f.map_lie, map_zero, hc]
  refine ⟨g, le_antisymm ?_ hUle⟩
  rintro _ ⟨a, ha, rfl⟩
  apply (hcU (f a)).1
  intro z hz
  obtain ⟨b, hb, rfl⟩ := hUle hz
  change ⁅f a, f b⁆ = 0
  rw [← f.map_lie, (hcT a).2 ha b hb, map_zero]

end
end ThirteenPlanes.Cartan
