/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.GradedRecutAction
public import ThirteenPlanes.Cartan.DerivationGradingAlbertMetric
public import Glennie.Compactness
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

set_option backward.privateInPublic true

/-! Maximizing the represented trace pairing over the actual compact Albert automorphisms. -/

namespace ThirteenPlanes.Cartan

open scoped RealInnerProductSpace

noncomputable section

abbrev AlbertContinuousEnd := Glennie.Albert →L[ℝ] Glennie.Albert

local instance : NormedRing AlbertContinuousEnd := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing AlbertContinuousEnd :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance : Module.Finite ℝ AlbertContinuousEnd :=
  Module.Finite.of_surjective (LinearMap.toContinuousLinearMap :
    Module.End ℝ Glennie.Albert ≃ₗ[ℝ] AlbertContinuousEnd).toLinearMap
    LinearMap.toContinuousLinearMap.surjective

/-- Trace as a continuous linear functional on the actual Albert endomorphisms. -/
def albertOperatorTrace : AlbertContinuousEnd →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ Glennie.Albert).comp (LinearMap.toContinuousLinearMap :
    Module.End ℝ Glennie.Albert ≃ₗ[ℝ] AlbertContinuousEnd).symm.toLinearMap).toContinuousLinearMap

/-- The underlying continuous map of a real Albert derivation. -/
abbrev nativeAlbertDerivationCLM (D : NativeAlbertDerivations) : AlbertContinuousEnd :=
  LinearMap.toContinuousLinearMap D.val

private def columnCLM : Glennie.AutomorphismColumns →L[ℝ] AlbertContinuousEnd :=
  ((LinearMap.toContinuousLinearMap : Module.End ℝ Glennie.Albert ≃ₗ[ℝ]
    AlbertContinuousEnd).toLinearMap.comp (Glennie.automorphismBasis.constr ℝ).toLinearMap).toContinuousLinearMap

private theorem columnCLM_apply (v : Glennie.AutomorphismColumns) (x : Glennie.Albert) :
    columnCLM v x = Glennie.columnMap v x := rfl

private theorem columnCLM_automorphism (g : Glennie.CompactAutomorphism) :
    columnCLM g.columns = g.equiv.toLinearMap.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact g.columns_apply x

private theorem star_albertAutomorphism (g : Glennie.CompactAutomorphism) :
    star (g.equiv.toLinearMap.toContinuousLinearMap : AlbertContinuousEnd) =
      g.equiv.symm.toLinearMap.toContinuousLinearMap := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪x, g.equiv y⟫ = ⟪g.equiv.symm x, y⟫
  rw [Glennie.hilbert_inner_eq_native, Glennie.hilbert_inner_eq_native, ← g.inner_map (g.equiv.symm x) y,
    g.equiv.apply_symm_apply]

private def pairingObjective (X Y : NativeAlbertDerivations) (v : Glennie.AutomorphismColumns) : ℝ :=
  -albertOperatorTrace (columnCLM v * nativeAlbertDerivationCLM X * star (columnCLM v) * nativeAlbertDerivationCLM Y)

private theorem pairingObjective_continuous (X Y : NativeAlbertDerivations) :
    Continuous (pairingObjective X Y) := by
  apply Continuous.neg
  exact albertOperatorTrace.continuous.comp
    (((columnCLM.continuous.mul continuous_const).mul
      (continuous_star.comp columnCLM.continuous)).mul continuous_const)

private theorem pairingObjective_columns (g : Glennie.CompactAutomorphism) (X Y : NativeAlbertDerivations) :
    pairingObjective X Y g.columns = nativeAlbertTracePairing (nativeAlbertLieAction g X) Y := by
  rw [pairingObjective, columnCLM_automorphism, star_albertAutomorphism, nativeAlbertTracePairing_apply]
  rfl

/-- The represented trace pairing of a moved derivation with another attains its maximum
on the actual compact Albert automorphisms. -/
theorem exists_nativeAlbertTracePairing_maximum (X Y : NativeAlbertDerivations) :
    ∃ g : Glennie.CompactAutomorphism, ∀ h : Glennie.CompactAutomorphism,
      nativeAlbertTracePairing (nativeAlbertLieAction h X) Y ≤
        nativeAlbertTracePairing (nativeAlbertLieAction g X) Y := by
  obtain ⟨v, hv, hmax⟩ := Glennie.automorphismMaps_compact.exists_isMaxOn
    Glennie.automorphismMaps_nonempty (pairingObjective_continuous X Y).continuousOn
  let g := Glennie.compactAutomorphismOfMap v hv
  have hg : g.columns = v := by
    funext i
    change (Glennie.compactAutomorphismOfMap v hv).equiv (Glennie.automorphismBasis i) = v i
    rw [Glennie.compactAutomorphismOfMap_apply, Glennie.columnMap_basis]
  refine ⟨g, fun h => ?_⟩
  have hh : pairingObjective X Y h.columns ≤ pairingObjective X Y g.columns := hg.symm ▸ hmax h.columns_mem
  rw [pairingObjective_columns, pairingObjective_columns] at hh
  exact hh

/-- Actual Albert conjugation preserves the trace pairing on the compact derivation algebra. -/
theorem nativeAlbertLieAction_tracePairing (g : Glennie.CompactAutomorphism) (X Y : NativeAlbertDerivations) :
    nativeAlbertTracePairing (nativeAlbertLieAction g X) (nativeAlbertLieAction g Y) =
      nativeAlbertTracePairing X Y := by
  simp only [nativeAlbertTracePairing_apply, nativeAlbertLieAction_val, ← conj_mul,
    LinearMap.trace_conj']

end
end ThirteenPlanes.Cartan
