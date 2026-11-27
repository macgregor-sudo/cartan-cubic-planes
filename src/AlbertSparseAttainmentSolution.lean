/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertCarrierBridge
public import ThirteenPlanes.Graded.Incidence
public import ThirteenPlanes.Shares.NativeTraceFrames

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

namespace Challenge

open ThirteenPlanes ThirteenPlanes.RoundCubics

private def independentFrameFamily (c : TightNativeCode) (i : Fin 13) (a : Fin 3) : Hermitian3 :=
  glennieAlbertEquiv.symm (c.point i a)

@[simp] private theorem nativePoint (c : TightNativeCode) (i : Fin 13) (a : Fin 3) :
    glennieAlbertEquiv (independentFrameFamily c i a) = c.point i a :=
  glennieAlbertEquiv.apply_symm_apply _

/-- The share used by the independent statement is the projection share on each distinct triple. -/
theorem albertFrameShare_eq_nativeProjection (c : TightNativeCode) {i j k : Fin 13}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    albertFrameShare (independentFrameFamily c i) (independentFrameFamily c j)
      (independentFrameFamily c k) = planeShare nativeEqualCubic c.decomposition i j k := by
  rw [planeShare_eq_shareOfThreePlanes]
  change _ = shareOfThreePlanes nativeEqualCubic (nativeFramePlane (c.point i))
    (nativeFramePlane (c.point j)) (nativeFramePlane (c.point k))
  rw [native_shareOfThreePlanes_eq_frame_trace (c.frame i) (c.frame j) (c.frame k)
    (c.planes_orthogonal hij) (c.planes_orthogonal hik) (c.planes_orthogonal hjk)]
  simp only [albertFrameShare, ← glennieAlbertEquiv_trace, glennieAlbertEquiv_jordan, nativePoint]

/-- Some thirteen-plane system in the Albert algebra has exactly 52 positive shares. -/
theorem albertSparseSystem_exists :
    ∃ F : Fin 13 → Fin 3 → Hermitian3, SparseAlbertSystem F := by
  classical
  obtain ⟨c, hc⟩ := Graded.native_frames_exist_fifty_two_shares
  refine ⟨independentFrameFamily c, ?_, ?_, ?_⟩
  · intro i
    exact (albertFrame_iff_glennieFrame _).mpr (by simpa only [nativePoint] using c.frame i)
  · intro i j hij
    exact (albertUnbiased_iff_inner _ _).mpr (by simpa only [nativePoint] using c.overlap hij)
  · have equal : (Finset.univ.filter (fun t : IncreasingTriple 13 =>
        0 < albertFrameShare (independentFrameFamily c t.val.1)
          (independentFrameFamily c t.val.2.1) (independentFrameFamily c t.val.2.2))) =
        positivePlaneTriples nativeEqualCubic c.decomposition := by
      apply Finset.ext
      intro t
      rw [positivePlaneTriples, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, unorderedPlaneShare,
        albertFrameShare_eq_nativeProjection c t.property.1.ne
          (t.property.1.trans t.property.2).ne t.property.2.ne]
    rw [equal]
    exact hc

end Challenge
