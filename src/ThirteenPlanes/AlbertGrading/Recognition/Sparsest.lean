module

public import ThirteenPlanes.AlbertGrading.Recognition.Transport

@[expose] public section

/-! Existence and uniqueness up to automorphism at 52 positive shares.

The reference graded example is `Graded.native_frames_exist_fifty_two_shares`.
The native-to-first-Tits isomorphism `nativeCompactTitsEquiv` and the normalization
`core_normalize` carry each extremal system to the reference system. Composing the two
normalizations gives one automorphism matching all 39 idempotents up to relabelling
the frames and their outcomes. The required pair normalization follows from the
octonionic normal form and transitivity on imaginary octonion units. -/

open scoped Matrix BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits RoundCubics

/-- The graded system of the first-Tits grading and Weyl basis, pulled back to `𝔸`. -/
def refPoint (m : Fin 13) (b : Fin 3) : Glennie.Albert :=
  nativeCompactTitsEquiv.symm (gradedFrame (pointRep m) b)

/-- A trace-preserving automorphism of `J_T`, read in `𝔸`. -/
def nativeAut (f : CompactTits ≃ₗ[ℝ] CompactTits) (hf : IsTraceAut f) :
    Glennie.CompactAutomorphism where
  equiv := nativeCompactTitsEquiv.toLinearEquiv.trans
    (f.trans nativeCompactTitsEquiv.symm.toLinearEquiv)
  map_jordan x y := by
    apply nativeCompactTitsEquiv.injective
    rw [nativeCompactTitsEquiv_product]
    simp only [LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
    rw [nativeCompactTitsEquiv_product, hf.1]
  map_trace x := by
    simp only [LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← nativeCompactTitsEquiv_trace, LinearIsometryEquiv.apply_symm_apply, hf.2,
      nativeCompactTitsEquiv_trace]

theorem normal_form (hN : OrbitHypotheses.PairNormalization) (c : TightNativeCode)
    (h52 : (positivePlaneTriples nativeEqualCubic c.decomposition).card = 52) :
    ∃ φ : Glennie.CompactAutomorphism, ∃ σ : Equiv.Perm (Fin 13),
      ∃ τ : Fin 13 → Equiv.Perm (Fin 3), ∀ i a, φ.equiv (c.point i a) = refPoint (σ i) (τ i a) := by
  classical
  obtain ⟨f, hf, σ, hσ⟩ := core_normalize hN (toTits_system c h52)
  have hS' := (toTits_system c h52).map hf
  have hex : ∀ i (a : ZMod 3), ∃ b : ZMod 3,
      f (toTits c i a) = gradedFrame (pointRep (σ i)) b := by
    intro i a
    have : f (toTits c i a) ∈ Set.range (gradedFrame (pointRep (σ i))) := by
      rw [← hσ i]; exact Set.mem_range_self a
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.symm⟩
  choose τ' hτ' using hex
  have hinj : ∀ i, Function.Injective (τ' i) := by
    intro i a₁ a₂ h
    apply frame_injective (hS'.frame i)
    change f (toTits c i a₁) = f (toTits c i a₂)
    rw [hτ', hτ', h]
  let τ : Fin 13 → Equiv.Perm (Fin 3) := fun i =>
    Equiv.ofBijective (τ' i) (Finite.injective_iff_bijective.mp (hinj i))
  refine ⟨nativeAut f hf, σ, τ, fun i a => ?_⟩
  exact congrArg nativeCompactTitsEquiv.symm (hτ' i a)

theorem sparsest_of_pairNormalization (hN : OrbitHypotheses.PairNormalization) : Statements.Sparsest := by
  refine ⟨Graded.native_frames_exist_fifty_two_shares, fun c c' h h' => ?_⟩
  obtain ⟨φ, σ, τ, hφ⟩ := normal_form hN c h
  obtain ⟨φ', σ', τ', hφ'⟩ := normal_form hN c' h'
  refine ⟨φ'.symm.comp φ, σ.trans σ'.symm,
    fun i => (τ i).trans (τ' (σ'.symm (σ i))).symm, fun i a => ?_⟩
  apply φ'.equiv.injective
  rw [Glennie.CompactAutomorphism.comp_apply, Glennie.CompactAutomorphism.symm_apply,
    LinearEquiv.apply_symm_apply, hφ, hφ']
  simp

end

end ThirteenPlanes.AlbertGrading
