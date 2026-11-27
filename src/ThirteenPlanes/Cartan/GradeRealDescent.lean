module

public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true

/-! Real subalgebras obtained from conjugation-stable homogeneous summands. -/

namespace ThirteenPlanes.Cartan

open LieAlgebra

noncomputable section

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K]

namespace LieComplex

/-- Real and imaginary parts give two copies of the chosen real subalgebra. -/
private def extendParts (T : LieSubalgebra ℝ K) : extend T ≃ₗ[ℝ] T × T where
  toFun x := (⟨realPart x.val, x.property.1⟩, ⟨imagPart x.val, x.property.2⟩)
  invFun p := ⟨ofReal p.1.val + Complex.I • ofReal p.2.val, by
    rw [mem_extend]
    simp [realPart_smul, imagPart_smul]⟩
  left_inv x := Subtype.ext (decompose_smul x.val)
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [realPart_smul, imagPart_smul]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ x.val y.val
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_smul _ r x.val

/-- Descent of a stable complex summand preserves dimension, with the field changed to real. -/
theorem descend_finrank_eq_of_stable [Module.Finite ℝ K] (H : LieSubalgebra ℂ (LieComplex K))
    (hH : Set.MapsTo conjugation (H : Set (LieComplex K)) (H : Set (LieComplex K))) :
    Module.finrank ℝ (descend H) = Module.finrank ℂ H := by
  let T := descend H
  have hparts := (extendParts T).finrank_eq
  rw [Module.finrank_prod, extend_descend_of_stable H hH] at hparts
  have htwice := Module.finrank_mul_finrank ℝ ℂ H
  rw [Complex.finrank_real_complex] at htwice
  change Module.finrank ℝ T = _
  omega

/-- An abelian, self-centralizing complex subalgebra descends to one with the same property. -/
theorem descend_selfCentralizing (H : LieSubalgebra ℂ (LieComplex K))
    (hst : Set.MapsTo conjugation (H : Set (LieComplex K)) (H : Set (LieComplex K)))
    (hc : ∀ x : LieComplex K, (∀ y ∈ H, ⁅x, y⁆ = 0) ↔ x ∈ H) :
    IsCompactCartan (descend H) := by
  intro x
  constructor
  · intro hx
    apply (hc (ofReal x)).mp
    intro z hz
    have ht : z ∈ extend (descend H) := by
      rw [extend_descend_of_stable H hst]
      exact hz
    obtain ⟨hr, hi⟩ := (mem_extend _ _).mp ht
    have h1 : ⁅(ofReal x : LieComplex K), ofReal (realPart z)⁆ = 0 := by
      rw [← LieHom.map_lie, hx _ hr, map_zero]
    have h2 : ⁅(ofReal x : LieComplex K), ofReal (imagPart z)⁆ = 0 := by
      rw [← LieHom.map_lie, hx _ hi, map_zero]
    let L : LieComplex K →ₗ[ℂ] LieComplex K :=
      LieModule.toEnd ℂ (LieComplex K) (LieComplex K) (ofReal x)
    change L z = 0
    have h1' : L (ofReal (realPart z)) = 0 := h1
    have h2' : L (ofReal (imagPart z)) = 0 := h2
    rw [← decompose_smul z, map_add, map_smul, h1', h2', smul_zero, add_zero]
  · intro hx y hy
    apply ofReal_injective
    rw [LieHom.map_lie, map_zero]
    exact (hc (ofReal x)).mpr hx (ofReal y) hy

private theorem descend_map_mem_iSup {ι : Type*} (H : ι → LieSubalgebra ℂ (LieComplex K))
    {x : K} (hx : x ∈ ⨆ i, (descend (H i)).toSubmodule) :
    ofReal x ∈ ⨆ i, (H i).toSubmodule := by
  refine Submodule.iSup_induction _ (motive := fun y => ofReal y ∈
    ⨆ i, (H i).toSubmodule) hx ?_ ?_ ?_
  · intro i y hy
    exact Submodule.mem_iSup_of_mem i hy
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- A complete complex splitting descends to a complete real splitting when each summand
is stable under conjugation. -/
theorem descend_isInternal_of_stable {ι : Type*} [DecidableEq ι]
    (H : ι → LieSubalgebra ℂ (LieComplex K))
    (hst : ∀ i, Set.MapsTo conjugation (H i : Set (LieComplex K)) (H i : Set (LieComplex K)))
    (hs : DirectSum.IsInternal (fun i => (H i).toSubmodule)) :
    DirectSum.IsInternal (fun i => (descend (H i)).toSubmodule) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro i
    apply Submodule.disjoint_def.mpr
    intro x hxi hx
    have hC := (iSupIndep_def.mp hs.submodule_iSupIndep) i
    apply ofReal_injective
    rw [map_zero]
    apply (Submodule.disjoint_def.mp hC) (ofReal x) hxi
    let outside := fun j : {j : ι // j ≠ i} => H j.val
    have hxs : x ∈ ⨆ j : {j : ι // j ≠ i}, (descend (outside j)).toSubmodule := by
      rw [iSup_subtype]
      exact hx
    simpa only [outside, iSup_subtype] using descend_map_mem_iSup outside hxs
  · rw [eq_top_iff]
    intro x _
    have he : ofReal x ∈ ⨆ i, (H i).toSubmodule := by
      rw [hs.submodule_iSup_eq_top]
      trivial
    suffices h : realPart (ofReal x) ∈ ⨆ i, (descend (H i)).toSubmodule by simpa using h
    refine Submodule.iSup_induction _ (motive := fun z => realPart z ∈
      ⨆ i, (descend (H i)).toSubmodule) he ?_ ?_ ?_
    · intro i z hz
      have hz' : z ∈ extend (descend (H i)) := by
        rw [extend_descend_of_stable _ (hst i)]
        exact hz
      exact Submodule.mem_iSup_of_mem i hz'.1
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- The actual Killing pairings vanish on the real pieces if they vanish on the
corresponding complex pieces. -/
theorem killing_orthogonal_descend [Module.Finite ℝ K] {ι : Type*}
    (H : ι → LieSubalgebra ℂ (LieComplex K))
    (h : Pairwise fun i j => ∀ x ∈ H i, ∀ y ∈ H j, killingForm ℂ (LieComplex K) x y = 0) :
    Pairwise fun i j => ∀ x ∈ descend (H i), ∀ y ∈ descend (H j), killingForm ℝ K x y = 0 := by
  intro i j hij x hx y hy
  have he := h hij (ofReal x) hx (ofReal y) hy
  rwa [killing_ofReal, Complex.ofReal_eq_zero] at he

end LieComplex

/-- An abelian self-centralizing real subalgebra is a Cartan in a Lie algebra with a
definite invariant pairing. -/
theorem cartan_of_definiteInvariant [Module.Finite ℝ K]
    (B : LinearMap.BilinForm ℝ K) (hdef : ∀ x, B x x = 0 → x = 0)
    (hinv : ∀ x y z : K, B ⁅x, y⁆ z = B x ⁅y, z⁆)
    (T : LieSubalgebra ℝ K) (hc : IsCompactCartan T) :
    T.IsCartanSubalgebra := by
  have : IsLieAbelian T := ⟨fun x y => Subtype.ext ((hc x.val).mpr x.property y.val y.property)⟩
  refine ⟨inferInstance, le_antisymm ?_ T.le_normalizer⟩
  intro x hx
  apply (hc x).mp
  intro y hy
  have hb : ⁅x, y⁆ ∈ T := (T.mem_normalizer_iff x).mp hx y hy
  apply hdef
  rw [hinv, (hc y).mpr hy _ hb, map_zero]

end

end ThirteenPlanes.Cartan
