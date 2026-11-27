/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.CubicRotation
public import ThirteenPlanes.Cartan.OperatorExponential
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! For an invariant Euclidean Lie algebra, an orthogonal Lie automorphism moves any given
vector to a vector commuting with a second prescribed vector. -/

namespace ThirteenPlanes.Cartan

open LieAlgebra NormedSpace ChargeFixed
open scoped RealInnerProductSpace

noncomputable section

section Differentiation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

local instance : NormedAlgebra ℚ (V →L[ℝ] V) := NormedAlgebra.restrictScalars ℚ ℝ _

omit [CompleteSpace V] in
private theorem exp_zero_smul_apply (B : V →L[ℝ] V) (x : V) : exp ((0 : ℝ) • B) x = x := by
  rw [zero_smul, exp_zero, one_apply_eq_self]

private theorem exp_pairing_hasDerivAt (B : V →L[ℝ] V) (x y : V) :
    HasDerivAt (fun t : ℝ => ⟪y, exp (t • B) x⟫) ⟪y, B x⟫ 0 := by
  have h := hasDerivAt_exp_smul_const B (0 : ℝ)
  rw [zero_smul, exp_zero, one_mul] at h
  let f := (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ V x)
  exact f.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

end Differentiation

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K] [Module.Finite ℝ K]

@[instance_reducible] private def negativeKillingCore (hK : CompactKilling K) : InnerProductSpace.Core ℝ K where
  inner a b := -killingForm ℝ K a b
  conj_inner_symm a b := by
    simp only [RCLike.conj_to_real]
    exact congrArg Neg.neg (LieModule.traceForm_comm ℝ K K b a)
  re_inner_nonneg a := by
    change 0 ≤ -killingForm ℝ K a a
    by_cases h : a = 0
    · subst a
      simp
    · exact neg_nonneg.mpr (hK a h).le
  add_left a b c := by simp [add_comm]
  smul_left a b r := by simp
  definite a h := by
    by_contra ha
    exact (hK a ha).ne (neg_eq_zero.mp h)

section KillingMetric

variable [Fact (CompactKilling K)]

local instance : InnerProductSpace.Core ℝ K := negativeKillingCore Fact.out
local instance : NormedAddCommGroup K := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
local instance : InnerProductSpace ℝ K := InnerProductSpace.ofCore (𝕜 := ℝ) (F := K) inferInstance
local instance : CompleteSpace K := FiniteDimensional.completeSpace ℝ K

local instance : Module.Finite ℝ (K →L[ℝ] K) :=
  Module.Finite.of_surjective (LinearMap.toContinuousLinearMap : (K →ₗ[ℝ] K) ≃ₗ[ℝ] (K →L[ℝ] K)).toLinearMap
    LinearMap.toContinuousLinearMap.surjective

local instance : NormedRing (K →L[ℝ] K) := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing (K →L[ℝ] K) := NonUnitalSeminormedRing.toIsTopologicalRing
local instance : ProperSpace (K →L[ℝ] K) := FiniteDimensional.proper_real _

local instance : NormedAlgebra ℚ (K →L[ℝ] K) := NormedAlgebra.restrictScalars ℚ ℝ _

private def adjointLinear : K →ₗ[ℝ] (K →ₗ[ℝ] K) :=
  LinearMap.mk₂ ℝ (fun x y => ⁅x, y⁆) (fun _ _ _ => add_lie ..)
    (fun _ _ _ => smul_lie ..) (fun _ _ _ => lie_add ..) (fun _ _ _ => lie_smul ..)

private def adjointCLM : K →L[ℝ] (K →L[ℝ] K) :=
  ((LinearMap.toContinuousLinearMap : (K →ₗ[ℝ] K) ≃ₗ[ℝ] (K →L[ℝ] K)).toLinearMap.comp
    adjointLinear).toContinuousLinearMap

@[simp] private theorem adjointCLM_apply (x y : K) : adjointCLM x y = ⁅x, y⁆ := rfl

private theorem continuous_bracket : Continuous (fun p : K × K => ⁅p.1, p.2⁆) := by
  change Continuous (fun p : K × K => adjointCLM p.1 p.2)
  exact (adjointCLM.continuous.comp continuous_fst).clm_apply continuous_snd

private theorem exp_ad_preserves_lie (z : K) (t : ℝ) (x y : K) :
    exp (t • adjointCLM z) ⁅x, y⁆ =
      ⁅exp (t • adjointCLM z) x, exp (t • adjointCLM z) y⁆ := by
  let A := t • adjointCLM z
  have hinter (w : K) : adjointCLM (A w) = commutatorOperator A (adjointCLM w) := by
    apply ContinuousLinearMap.ext
    intro a
    change ⁅t • ⁅z, w⁆, a⁆ = t • ⁅z, ⁅w, a⁆⁆ - ⁅w, t • ⁅z, a⁆⁆
    rw [smul_lie, lie_smul, ← smul_sub, leibniz_lie, add_sub_cancel_right]
  have h := @intertwines_exp K (K →L[ℝ] K) _ _ _ _ _ _ adjointCLM A
    (commutatorOperator A) hinter x
  rw [exp_commutatorOperator] at h
  have he := congrArg (fun f : K →L[ℝ] K => f (exp A y)) h
  have hinv : exp (-A) * exp A = 1 := by
    rw [← exp_add_of_commute (Commute.refl A).neg_left, neg_add_cancel, exp_zero]
  change ⁅exp A x, exp A y⁆ = exp A ⁅x, exp (-A) (exp A y)⁆ at he
  rw [← mul_apply_eq_comp, hinv, one_apply_eq_self] at he
  exact he.symm

private def orthogonalBracketMaps : Set (K →L[ℝ] K) :=
  {f | (∀ x, ‖f x‖ = ‖x‖) ∧ ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆}

private theorem orthogonalBracketMaps_isCompact :
    IsCompact (orthogonalBracketMaps : Set (K →L[ℝ] K)) := by
  have hnorm : IsClosed {f : K →L[ℝ] K | ∀ x : K, ‖f x‖ = ‖x‖} := by
    rw [show {f : K →L[ℝ] K | ∀ x : K, ‖f x‖ = ‖x‖} =
      ⋂ x : K, {f : K →L[ℝ] K | ‖f x‖ = ‖x‖} by ext f; simp]
    exact isClosed_iInter fun x => isClosed_eq
      (ContinuousLinearMap.apply ℝ K x).continuous.norm continuous_const
  have hlie : IsClosed {f : K →L[ℝ] K | ∀ x y : K, f ⁅x, y⁆ = ⁅f x, f y⁆} := by
    rw [show {f : K →L[ℝ] K | ∀ x y : K, f ⁅x, y⁆ = ⁅f x, f y⁆} =
      ⋂ (x : K) (y : K), {f : K →L[ℝ] K | f ⁅x, y⁆ = ⁅f x, f y⁆} by ext f; simp]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
      (ContinuousLinearMap.apply ℝ K ⁅x, y⁆).continuous
      (continuous_bracket.comp ((ContinuousLinearMap.apply ℝ K x).continuous.prodMk
        (ContinuousLinearMap.apply ℝ K y).continuous))
  have hb : (orthogonalBracketMaps : Set (K →L[ℝ] K)) ⊆ Metric.closedBall 0 1 := by
    intro f hf
    exact mem_closedBall_zero_iff.mpr (f.opNorm_le_bound zero_le_one (fun x => by rw [hf.1 x, one_mul]))
  exact (isCompact_closedBall 0 1).of_isClosed_subset (hnorm.inter hlie) hb

private theorem exp_ad_mem_orthogonalBracketMaps
    (hs : ∀ z : K, IsSkew (adjointLinear z)) (z : K) (t : ℝ) :
    exp (t • adjointCLM z) ∈ (orthogonalBracketMaps : Set (K →L[ℝ] K)) := by
  refine ⟨?_, exp_ad_preserves_lie z t⟩
  have h : IsSkew (t • (adjointLinear z)) := by
    intro a b
    change ⟪t • ⁅z, a⁆, b⟫ = -⟪a, t • ⁅z, b⁆⟫
    have hz : ⟪⁅z, a⁆, b⟫ = -⟪a, ⁅z, b⁆⟫ := hs z a b
    rw [real_inner_smul_left, real_inner_smul_right, hz, mul_neg]
  intro x
  have he : LinearMap.toContinuousLinearMap (t • (adjointLinear z)) = t • adjointCLM z := by
    ext w
    rfl
  simpa only [skewRotation_apply, he] using (skewRotation _ h).norm_map x

set_option maxHeartbeats 1200000 in
private theorem exists_lieEquiv_commutes_aux
    (hs : ∀ z : K, IsSkew (adjointLinear z)) (x y : K) :
    ∃ g : K ≃ₗ⁅ℝ⁆ K, ⁅g x, y⁆ = 0 := by
  have hn : (orthogonalBracketMaps : Set (K →L[ℝ] K)).Nonempty :=
    ⟨1, fun _ => rfl, fun _ _ => rfl⟩
  let objective : (K →L[ℝ] K) → ℝ := fun f => ⟪y, f x⟫
  have hc : Continuous objective :=
    ((innerSL ℝ y).continuous.comp (ContinuousLinearMap.apply ℝ K x).continuous)
  obtain ⟨f, hf, hm⟩ := orthogonalBracketMaps_isCompact.exists_isMaxOn hn hc.continuousOn
  have critical (z : K) : ⟪y, ⁅z, f x⁆⟫ = 0 := by
    have hmax : IsLocalMax (fun t : ℝ => ⟪y, exp (t • adjointCLM z) (f x)⟫) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      let e := exp (t • adjointCLM z)
      have he := exp_ad_mem_orthogonalBracketMaps hs z t
      have hef : e.comp f ∈ (orthogonalBracketMaps : Set (K →L[ℝ] K)) :=
        ⟨fun a => (he.1 (f a)).trans (hf.1 a),
          fun a b => by
            change e (f ⁅a, b⁆) = ⁅e (f a), e (f b)⁆
            rw [hf.2, he.2]⟩
      have hle : ⟪y, e (f x)⟫ ≤ ⟪y, f x⟫ := hm hef
      change ⟪y, e (f x)⟫ ≤ ⟪y, exp ((0 : ℝ) • adjointCLM z) (f x)⟫
      rw [exp_zero_smul_apply]
      exact hle
    exact hmax.hasDerivAt_eq_zero (exp_pairing_hasDerivAt (adjointCLM z) (f x) y)
  have hzero : ⁅f x, y⁆ = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    let z := ⁅f x, y⁆
    have hskew : ⟪⁅f x, z⁆, y⟫ = -⟪z, z⟫ := hs (f x) z y
    calc
      ⟪z, z⟫ = -⟪⁅f x, z⁆, y⟫ := by rw [hskew, neg_neg]
      _ = ⟪y, ⁅z, f x⁆⟫ := by rw [← inner_neg_left, lie_skew, real_inner_comm]
      _ = 0 := critical z
  let fi : K →ₗᵢ[ℝ] K := ⟨f.toLinearMap, hf.1⟩
  let fh : K →ₗ⁅ℝ⁆ K := { f.toLinearMap with map_lie' := fun {a b} => hf.2 a b }
  let g := LieEquiv.ofBijective fh ⟨fi.injective, (LinearMap.injective_iff_surjective).mp fi.injective⟩
  exact ⟨g, hzero⟩

end KillingMetric

/-- Any vector can be moved by a Lie automorphism to commute with a prescribed vector. -/
theorem compactKilling_exists_lieEquiv_commutes (hK : CompactKilling K) (x y : K) :
    ∃ g : K ≃ₗ⁅ℝ⁆ K, ⁅g x, y⁆ = 0 := by
  let : Fact (CompactKilling K) := ⟨hK⟩
  apply exists_lieEquiv_commutes_aux (K := K) _ x y
  intro z a b
  change -killingForm ℝ K ⁅z, a⁆ b = -(-killingForm ℝ K a ⁅z, b⁆)
  exact congrArg Neg.neg (LieModule.traceForm_apply_lie_apply' ℝ K K z a b)

end
end ThirteenPlanes.Cartan
