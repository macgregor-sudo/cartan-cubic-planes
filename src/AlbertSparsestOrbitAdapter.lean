/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertSparseAttainmentSolution
public import ThirteenPlanes.AlbertGrading.Recognition.Statements

@[expose] public section

noncomputable section

namespace Challenge

open ThirteenPlanes ThirteenPlanes.RoundCubics

/-- Map any independently defined family of thirteen pairwise unbiased frames into the native code type. -/
def toNativeFrameFamily (F : Fin 13 → Fin 3 → Hermitian3) (frames : ∀ i, AlbertFrame (F i))
    (unbiased : Pairwise (fun i j => AlbertUnbiased (F i) (F j))) : TightNativeCode where
  point i a := glennieAlbertEquiv (F i a)
  frame i := (albertFrame_iff_glennieFrame _).mp (frames i)
  overlap h := (albertUnbiased_iff_inner _ _).mp (unbiased h)

/-- An arbitrary sparse family in independent coordinates realizes a native code with the exact support count. -/
theorem sparseAlbertSystem_toNative (F : Fin 13 → Fin 3 → Hermitian3) (hF : SparseAlbertSystem F) :
    ∃ c : TightNativeCode, (∀ i a, c.point i a = glennieAlbertEquiv (F i a)) ∧
      (positivePlaneTriples nativeEqualCubic c.decomposition).card = 52 := by
  classical
  obtain ⟨frames, unbiased, support⟩ := hF
  let c := toNativeFrameFamily F frames unbiased
  refine ⟨c, fun _ _ => rfl, ?_⟩
  have nativeShare {i j k : Fin 13} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      albertFrameShare (F i) (F j) (F k) = planeShare nativeEqualCubic c.decomposition i j k := by
    have point (i : Fin 13) : (fun a => glennieAlbertEquiv.symm (c.point i a)) = F i := by
      funext a
      exact glennieAlbertEquiv.symm_apply_apply (F i a)
    have h := albertFrameShare_eq_nativeProjection c hij hik hjk
    change albertFrameShare (fun a => glennieAlbertEquiv.symm (c.point i a))
      (fun a => glennieAlbertEquiv.symm (c.point j a))
      (fun a => glennieAlbertEquiv.symm (c.point k a)) = _ at h
    rwa [point, point, point] at h
  have equal : positivePlaneTriples nativeEqualCubic c.decomposition =
      Finset.univ.filter (fun t : IncreasingTriple 13 =>
        0 < albertFrameShare (F t.val.1) (F t.val.2.1) (F t.val.2.2)) := by
    apply Finset.ext
    intro t
    rw [positivePlaneTriples, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, unorderedPlaneShare,
      nativeShare t.property.1.ne (t.property.1.trans t.property.2).ne t.property.2.ne]
  rw [equal]
  exact support

/-- Transport of an actual native orbit classification to the independent Albert model. -/
theorem albertSparsestSystem_of_native (native : AlbertGrading.Statements.Sparsest) :
    (∃ F : Fin 13 → Fin 3 → Hermitian3, SparseAlbertSystem F) ∧
    (∀ F G : Fin 13 → Fin 3 → Hermitian3, SparseAlbertSystem F → SparseAlbertSystem G →
      ∃ (φ : Hermitian3 ≃ₗ[ℝ] Hermitian3) (σ : Equiv.Perm (Fin 13))
        (τ : Fin 13 → Equiv.Perm (Fin 3)),
        φ hermitianOne = hermitianOne ∧
        (∀ x y, φ (jordanMul x y) = jordanMul (φ x) (φ y)) ∧
        ∀ i a, φ (F i a) = G (σ i) (τ i a)) := by
  refine ⟨albertSparseSystem_exists, ?_⟩
  intro F G hF hG
  obtain ⟨c, hc, hc52⟩ := sparseAlbertSystem_toNative F hF
  obtain ⟨d, hd, hd52⟩ := sparseAlbertSystem_toNative G hG
  obtain ⟨g, σ, τ, h⟩ := native.2 c d hc52 hd52
  let φ := (glennieAlbertEquiv.trans g.equiv).trans glennieAlbertEquiv.symm
  refine ⟨φ, σ, τ, ?_, ?_, ?_⟩
  · apply glennieAlbertEquiv.injective
    simp only [φ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      glennieAlbertEquiv_one, g.map_unit]
  · intro x y
    apply glennieAlbertEquiv.injective
    simp only [φ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      glennieAlbertEquiv_jordan, g.map_jordan]
  · intro i a
    apply glennieAlbertEquiv.injective
    simpa only [hc, hd, φ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using h i a

end Challenge
