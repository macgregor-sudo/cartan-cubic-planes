/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlbertCarrierBridge
public import ThirteenPlanes.AlbertGrading.Completion.Completion

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

namespace Challenge

open ThirteenPlanes ThirteenPlanes.AlbertGrading

private abbrev toNativePlane (P : Submodule ℝ TracelessHermitian3) : Submodule ℝ NativeTraceless :=
  P.map glennieTracelessEquiv.toLinearMap

private abbrev independentPlane (Q : Submodule ℝ NativeTraceless) : Submodule ℝ TracelessHermitian3 :=
  Q.map glennieTracelessEquiv.symm.toLinearMap

@[simp] private theorem toNativePlane_independentPlane (Q : Submodule ℝ NativeTraceless) :
    toNativePlane (independentPlane Q) = Q :=
  (Submodule.map_symm_eq_iff glennieTracelessEquiv).1 rfl

private theorem mem_toNativePlane (P : Submodule ℝ TracelessHermitian3) (x : TracelessHermitian3) :
    glennieTracelessEquiv x ∈ toNativePlane P ↔ x ∈ P := by
  constructor
  · rintro ⟨y, hy, h⟩
    rwa [glennieTracelessEquiv.injective h] at hy
  · intro hx
    exact Submodule.mem_map_of_mem hx

private theorem centeredProduct_coe (x y : TracelessHermitian3) :
    ((nativeEqualCubic.L (glennieTracelessEquiv x) (glennieTracelessEquiv y)) : Glennie.Albert) =
      glennieAlbertEquiv (jordanMul x y - (jordanTrace (jordanMul x y) / 3) • hermitianOne) := by
  change Glennie.traceless (Glennie.jordan (glennieAlbertEquiv x) (glennieAlbertEquiv y)) = _
  simp only [Glennie.traceless, map_sub, map_smul, glennieAlbertEquiv_jordan, glennieAlbertEquiv_one,
    ← glennieAlbertEquiv_trace]

private theorem closedAlbertPlane_iff (P : Submodule ℝ TracelessHermitian3) :
    ClosedAlbertPlane P ↔
      Module.finrank ℝ (toNativePlane P) = 2 ∧ IsClosedPiece nativeEqualCubic (toNativePlane P) := by
  rw [glennieTracelessEquiv.finrank_map_eq P]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro h u v hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨z, hz, he⟩ := h x hx y hy
    refine ⟨z, hz, Subtype.ext ?_⟩
    change glennieAlbertEquiv z =
      ((nativeEqualCubic.L (glennieTracelessEquiv x) (glennieTracelessEquiv y)) : Glennie.Albert)
    rw [centeredProduct_coe, he]
  · intro h x hx y hy
    let w := nativeEqualCubic.L (glennieTracelessEquiv x) (glennieTracelessEquiv y)
    let z := glennieTracelessEquiv.symm w
    have hz : glennieTracelessEquiv z = w := glennieTracelessEquiv.apply_symm_apply w
    refine ⟨z, (mem_toNativePlane P z).mp (hz ▸ ?_), ?_⟩
    · exact h ((mem_toNativePlane P x).mpr hx) ((mem_toNativePlane P y).mpr hy)
    · apply glennieAlbertEquiv.injective
      rw [← glennieTracelessEquiv_apply, hz, centeredProduct_coe]

private theorem albertPlaneOrthogonal_iff (P Q : Submodule ℝ TracelessHermitian3) :
    AlbertPlaneOrthogonal P Q ↔ (toNativePlane P).IsOrtho (toNativePlane Q) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  have hinner (x y : TracelessHermitian3) :
      inner ℝ (glennieTracelessEquiv x) (glennieTracelessEquiv y) = jordanTrace (jordanMul x y) := by
    rw [Submodule.coe_inner, Glennie.hilbert_inner_eq_native]
    simp only [Glennie.inner, glennieTracelessEquiv_apply, ← glennieAlbertEquiv_jordan,
      glennieAlbertEquiv_trace]
  constructor
  · intro h u hu v hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    change inner ℝ (glennieTracelessEquiv x) (glennieTracelessEquiv y) = 0
    rw [hinner]
    exact h x hx y hy
  · intro h x hx y hy
    rw [← hinner]
    exact h _ ((mem_toNativePlane P x).mpr hx) _ ((mem_toNativePlane Q y).mpr hy)

/-- The independent completion statement, transported from the checked native theorem. -/
theorem albertCompletion :
    (∀ F : Fin 12 → Fin 3 → Hermitian3, (∀ i, AlbertFrame (F i)) →
      Pairwise (fun i j => AlbertUnbiased (F i) (F j)) →
      ∃ q : Fin 3 → Hermitian3, AlbertFrame q ∧ (∀ i, AlbertUnbiased (F i) q) ∧
        ∀ q' : Fin 3 → Hermitian3, AlbertFrame q' → (∀ i, AlbertUnbiased (F i) q') →
          Set.range q' = Set.range q) ∧
    (∀ P : Fin 12 → Submodule ℝ TracelessHermitian3, (∀ i, ClosedAlbertPlane (P i)) →
      Pairwise (fun i j => AlbertPlaneOrthogonal (P i) (P j)) →
      ∃! Q : Submodule ℝ TracelessHermitian3,
        ClosedAlbertPlane Q ∧ ∀ i, AlbertPlaneOrthogonal (P i) Q) := by
  constructor
  · intro F hF unbiased
    let e := glennieAlbertEquiv
    let F' : Fin 12 → Fin 3 → Glennie.Albert := fun i a => e (F i a)
    obtain ⟨q, hq, hunb, unique⟩ := completionO_frames F'
      (fun i => (albertFrame_iff_glennieFrame (F i)).mp (hF i))
      (fun i j hij => (albertUnbiased_iff_inner (F i) (F j)).mp (unbiased hij))
    let Q : Fin 3 → Hermitian3 := fun a => e.symm (q a)
    have hQ : ∀ a, glennieAlbertEquiv (Q a) = q a := fun a => e.apply_symm_apply (q a)
    refine ⟨Q, (albertFrame_iff_glennieFrame Q).mpr ?_, fun i => (albertUnbiased_iff_inner _ _).mpr ?_, ?_⟩
    · simpa only [hQ] using hq
    · simpa only [hQ, NativeUnbiased, F'] using hunb i
    · intro Q' hQ' unbQ'
      have eq := unique (fun a => e (Q' a)) ((albertFrame_iff_glennieFrame Q').mp hQ')
        (fun i => (albertUnbiased_iff_inner (F i) Q').mp (unbQ' i))
      have eq' := congrArg (fun S : Set Glennie.Albert => e.symm '' S) eq
      simpa only [← Set.range_comp, Function.comp_def, e.symm_apply_apply, Q] using eq'
  · intro P hP orth
    let P' : Fin 12 → Submodule ℝ NativeTraceless := fun i => toNativePlane (P i)
    have hdim (i) : Module.finrank ℝ (P' i) = 2 := ((closedAlbertPlane_iff _).mp (hP i)).1
    have hclosed (i) : IsClosedPiece nativeEqualCubic (P' i) := ((closedAlbertPlane_iff _).mp (hP i)).2
    have horth : Pairwise (fun i j => (P' i).IsOrtho (P' j)) :=
      fun i j hij => (albertPlaneOrthogonal_iff _ _).mp (orth hij)
    let W := (⨆ i, P' i)ᗮ
    let Q := independentPlane W
    have hQ : toNativePlane Q = W := toNativePlane_independentPlane W
    obtain ⟨q, hq, hplane⟩ := complement_isFramePlane P' hdim hclosed horth
    have hWclosed : IsClosedPiece nativeEqualCubic W := by
      change IsClosedPiece nativeEqualCubic (⨆ i, P' i)ᗮ
      rw [← hplane]
      exact framePlane_closed hq
    have hWdim : Module.finrank ℝ W = 2 := complement_finrank P' hdim horth
    have hWorth (i : Fin 12) : (P' i).IsOrtho W :=
      (Submodule.isOrtho_iff_le.mpr (Submodule.orthogonal_le (le_iSup P' i))).symm
    refine ⟨Q, ⟨(closedAlbertPlane_iff Q).mpr ?_, fun i => (albertPlaneOrthogonal_iff _ _).mpr ?_⟩, ?_⟩
    · rw [hQ]; exact ⟨hWdim, hWclosed⟩
    · rw [hQ]; exact hWorth i
    · rintro R ⟨hR, hRo⟩
      apply Submodule.map_injective_of_injective glennieTracelessEquiv.injective
      change toNativePlane R = toNativePlane Q
      rw [hQ]
      exact eq_complement_of_orthogonal P' hdim horth _ ((closedAlbertPlane_iff R).mp hR).1
        (fun i => (albertPlaneOrthogonal_iff _ _).mp (hRo i))

/-- The existing graded Albert frames realize both hypotheses of the independent statement. -/
theorem albertCompletion_hypotheses_realized :
    (∃ F : Fin 12 → Fin 3 → Hermitian3, (∀ i, AlbertFrame (F i)) ∧
      Pairwise (fun i j => AlbertUnbiased (F i) (F j))) ∧
    (∃ P : Fin 12 → Submodule ℝ TracelessHermitian3, (∀ i, ClosedAlbertPlane (P i)) ∧
      Pairwise (fun i j => AlbertPlaneOrthogonal (P i) (P j))) := by
  obtain ⟨F, hF, hUnbiased⟩ := completionO_hypotheses_realized
  constructor
  · let G : Fin 12 → Fin 3 → Hermitian3 := fun i a => glennieAlbertEquiv.symm (F i a)
    have hG : ∀ i a, glennieAlbertEquiv (G i a) = F i a :=
      fun i a => glennieAlbertEquiv.apply_symm_apply (F i a)
    refine ⟨G, fun i => (albertFrame_iff_glennieFrame _).mpr ?_, fun i j hij =>
      (albertUnbiased_iff_inner _ _).mpr ?_⟩
    · simpa only [hG] using hF i
    · simpa only [hG, NativeUnbiased] using hUnbiased hij
  · let P' : Fin 12 → Submodule ℝ NativeTraceless := fun i => nativeFramePlane (F i)
    let P : Fin 12 → Submodule ℝ TracelessHermitian3 := fun i => independentPlane (P' i)
    have hP (i : Fin 12) : toNativePlane (P i) = P' i := toNativePlane_independentPlane _
    refine ⟨P, fun i => (closedAlbertPlane_iff _).mpr ?_, fun i j hij =>
      (albertPlaneOrthogonal_iff _ _).mpr ?_⟩
    · rw [hP]
      exact ⟨nativeFramePlane_dimension (hF i), framePlane_closed (hF i)⟩
    · rw [hP, hP]
      exact CompletionO.framePlanes_orthogonal (hF i) (hF j) (hUnbiased hij)

end Challenge
