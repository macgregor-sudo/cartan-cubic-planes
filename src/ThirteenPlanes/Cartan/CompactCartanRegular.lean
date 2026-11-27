/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition
public import Mathlib.Algebra.Lie.CartanExists

@[expose] public section

set_option backward.privateInPublic true

/-! Each compact Cartan is the centralizer of one of its elements. -/

namespace ThirteenPlanes.Cartan

open LieAlgebra LieSubalgebra Module

noncomputable section

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K]

private theorem compact_double_ad_eq_zero (hK : CompactKilling K) (x y : K)
    (h : ⁅x, ⁅x, y⁆⁆ = 0) : ⁅x, y⁆ = 0 := by
  have hk := LieModule.traceForm_apply_lie_apply' ℝ K K x y ⁅x, y⁆
  change killingForm ℝ K ⁅x, y⁆ ⁅x, y⁆ = -killingForm ℝ K y ⁅x, ⁅x, y⁆⁆ at hk
  rw [h, map_zero, neg_zero] at hk
  by_contra hn
  exact (hK _ hn).ne hk

private theorem compact_ad_pow_eq_zero (hK : CompactKilling K) (x y : K) (n : ℕ)
    (h : ((ad ℝ K x) ^ n) y = 0) : ⁅x, y⁆ = 0 := by
  induction n with
  | zero =>
    have hy : y = 0 := h
    simp [hy]
  | succ n ih =>
    cases n with
    | zero => simpa using h
    | succ n =>
      have hz : ⁅x, ⁅x, ((ad ℝ K x) ^ n) y⁆⁆ = 0 := by
        simpa only [pow_succ', mul_apply_eq_comp, ad_apply] using h
      apply ih
      rw [pow_succ', mul_apply_eq_comp, ad_apply]
      exact compact_double_ad_eq_zero hK _ _ hz

/-- Under the negative-definite Killing form, the Engel space is the actual centralizer. -/
theorem compact_mem_engel_iff (hK : CompactKilling K) (x y : K) :
    y ∈ engel ℝ x ↔ ⁅x, y⁆ = 0 := by
  rw [mem_engel_iff]
  exact ⟨fun ⟨n, hn⟩ => compact_ad_pow_eq_zero hK x y n hn,
    fun h => ⟨1, by simpa using h⟩⟩

variable [Module.Finite ℝ K]

/-- Every compact Cartan contains an element whose adjoint kernel is the Cartan itself. -/
theorem compactCartan_exists_centralizer (hK : CompactKilling K)
    (T : LieSubalgebra ℝ K) (hT : IsCompactCartan T) :
    ∃ x ∈ T, ∀ y : K, ⁅x, y⁆ = 0 ↔ y ∈ T := by
  let p (n : ℕ) : Prop := ∃ x ∈ T, Module.finrank ℝ (engel ℝ x) = n
  classical
  have hex : ∃ n, p n := ⟨_, 0, T.zero_mem, rfl⟩
  obtain ⟨x, hx, hr⟩ := Nat.find_spec hex
  let E : {engel ℝ z | z ∈ T} := ⟨engel ℝ x, x, hx, rfl⟩
  have hmin : IsMin E := by
    rintro ⟨_, y, hy, rfl⟩ hle
    have hdim : Module.finrank ℝ (engel ℝ x) ≤ Module.finrank ℝ (engel ℝ y) :=
      hr ▸ Nat.find_min' hex ⟨y, hy, rfl⟩
    change engel ℝ x ≤ engel ℝ y
    have hsame := Submodule.eq_of_le_of_finrank_le hle hdim
    exact (LieSubalgebra.toSubmodule_injective hsame).ge
  have hle : T ≤ E := fun y hy => (compact_mem_engel_iff hK x y).2 ((hT x).2 hx y hy)
  have hcard : (Module.finrank ℝ K : Cardinal) ≤ Cardinal.mk ℝ :=
    Cardinal.natCast_le_aleph0.trans (Cardinal.infinite_iff.mp inferInstance)
  have hbot := engel_isBot_of_isMin hcard T E hle hmin
  refine ⟨x, hx, fun y => ⟨?_, fun hy => (hT x).2 hx y hy⟩⟩
  intro hxy
  apply (hT y).1
  intro z hz
  have hEz : engel ℝ x ≤ engel ℝ z := hbot ⟨engel ℝ z, z, hz, rfl⟩
  have hz' := (compact_mem_engel_iff hK z y).1 (hEz ((compact_mem_engel_iff hK x y).2 hxy))
  rw [← lie_skew y z, hz', neg_zero]

end
end ThirteenPlanes.Cartan
