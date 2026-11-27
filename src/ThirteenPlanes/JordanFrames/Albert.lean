module

public import ThirteenPlanes.JordanFrames.Generic
public import ThirteenPlanes.Cartan.FramePlanes

@[expose] public section

/-! The frame-plane correspondence and capacity for the compact Albert algebra. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics

noncomputable section

/-- The native frame chart has the centered frame span as its image. -/
theorem native_framePlane_eq_centered_span {p : Fin 3 → Glennie.Albert}
    (hp : Glennie.Frame p) :
    nativeFramePlane p = Submodule.span ℝ (Set.range fun i => nativeCenter (p i)) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    change nativeCenter (∑ i, nativeFrameEntries u i • p i) ∈ _
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    let w : Fin 3 → ℝ := Pi.single i 1
    have hw : ∑ j, w j = 1 := by simp [w]
    have hpoint : nativeFrameSynthesis p w = p i := by simp [nativeFrameSynthesis, w, Pi.single_apply]
    have hsum : (∑ j, (w j - (∑ k, w k) / 3)) = 0 := by
      rw [Finset.sum_sub_distrib, hw]
      norm_num
    obtain ⟨v, hv⟩ := nativeFrameEntries_surjective_of_zero_sum _ hsum
    refine ⟨v, Subtype.ext ?_⟩
    rw [nativeFrameChart_coe hp, nativeCenter_coe, hv, ← hpoint, nativeFrameSynthesis_centered hp]

/-- The actual trace overlap of two Albert points after centering. -/
theorem native_frame_centered_inner {p q : Fin 3 → Glennie.Albert}
    (hp : Glennie.Frame p) (hq : Glennie.Frame q) (i j : Fin 3) :
    ⟪nativeCenter (p i), nativeCenter (q j)⟫ = Glennie.inner (p i) (q j) - 1 / 3 := by
  change Glennie.inner (Glennie.traceless (p i)) (nativeCenter (q j) : Glennie.Albert) = _
  rw [nativeInner_center_left, nativeCenter_coe, Glennie.traceless, hq.trace_one,
    Glennie.inner_sub_right, Glennie.inner_smul_right, nativeInner_one_right, hp.trace_one, mul_one]

/-- Albert frame planes are orthogonal exactly when all nine overlaps are one third. -/
theorem native_framePlane_orthogonal_iff {p q : Fin 3 → Glennie.Albert}
    (hp : Glennie.Frame p) (hq : Glennie.Frame q) :
    (nativeFramePlane p).IsOrtho (nativeFramePlane q) ↔
      ∀ i j, Glennie.inner (p i) (q j) = 1 / 3 := by
  rw [native_framePlane_eq_centered_span hp, native_framePlane_eq_centered_span hq,
    Submodule.isOrtho_span]
  constructor
  · intro h i j
    exact sub_eq_zero.mp ((native_frame_centered_inner hp hq i j).symm.trans
      (h ⟨i, rfl⟩ ⟨j, rfl⟩))
  · rintro h _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [native_frame_centered_inner hp hq, h, sub_self]

/-- Equality of existing Albert frame planes is precisely equality up to reordering the atoms. -/
theorem native_framePlane_eq_iff_relabel {p q : Fin 3 → Glennie.Albert}
    (hp : Glennie.Frame p) (hq : Glennie.Frame q) :
    nativeFramePlane p = nativeFramePlane q ↔
      ∃ σ : Equiv.Perm (Fin 3), ∀ i, q i = p (σ i) := by
  rw [native_framePlane_eq_centered_span hp, native_framePlane_eq_centered_span hq]
  constructor
  · intro heq
    have hspan := congrArg (fun S : Submodule ℝ NativeTraceless =>
      S.map Glennie.traceLinear.ker.subtype) heq
    simp only [Submodule.map_span, ← Set.range_comp] at hspan
    have hcenter {r : Fin 3 → Glennie.Albert} (hr : Glennie.Frame r) :
        Glennie.traceLinear.ker.subtype ∘ (fun i => nativeCenter (r i)) =
          fun i => r i - (1 / 3 : ℝ) • (1 : Glennie.Albert) := by
      funext i
      change Glennie.traceless (r i) = _
      rw [Glennie.traceless, hr.trace_one]
    rw [hcenter hp, hcenter hq] at hspan
    apply relabel_of_centered_span_eq Glennie.jordanLinear Glennie.traceLinear 1
      hp.trace_one hq.trace_one (nativeFrame_jordan hp) (nativeFrame_jordan hq) _ hspan
    simpa only [Fin.sum_univ_three] using hp.sum_unit
  · rintro ⟨σ, hσ⟩
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact ⟨σ.symm i, by dsimp only; rw [hσ, σ.apply_symm_apply]⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨σ i, by dsimp only; rw [hσ]⟩

/-- A closed two-plane in the native compact Albert trace-zero space is the plane
of a genuine Jordan frame, unique up to a permutation of its points. -/
theorem native_closedPlane_iff_frame (U : Submodule ℝ NativeTraceless)
    (dim : Module.finrank ℝ U = 2) :
    IsClosedPiece nativeEqualCubic U ↔
      ∃ p : Fin 3 → Glennie.Albert, Glennie.Frame p ∧ U = nativeFramePlane p ∧
        ∀ q : Fin 3 → Glennie.Albert, Glennie.Frame q → U = nativeFramePlane q →
          ∃ σ : Equiv.Perm (Fin 3), ∀ i, q i = p (σ i) := by
  constructor
  · intro hU
    obtain ⟨p, hp, hpU⟩ := Cartan.nativeClosedPlane_has_frame U dim hU
    exact ⟨p, hp, hpU, fun q hq hqU =>
      (native_framePlane_eq_iff_relabel hp hq).mp (hpU.symm.trans hqU)⟩
  · rintro ⟨p, hp, rfl, _⟩ x y hx hy
    exact nativeFramePlane_closed hp hx hy

set_option maxHeartbeats 800000 in
/-- The Albert corollary applies to arbitrary sets of actual frames. -/
theorem native_frameSet_capacity
    (S : Set {p : Fin 3 → Glennie.Albert // Glennie.Frame p})
    (orth : S.Pairwise fun p q => ∀ i j, Glennie.inner (p.val i) (q.val j) = 1 / 3) :
    S.Finite ∧ S.ncard ≤ 13 ∧
      ((⨆ f : S, nativeFramePlane f.val.val) = ⊤ ↔ S.ncard = 13) :=
by
  apply orthogonalPlaneSet_capacity (V := NativeTraceless) (m := 13)
    nativeTraceless_finrank (fun f : {p : Fin 3 → Glennie.Albert // Glennie.Frame p} =>
      nativeFramePlane f.val) (fun f => nativeFramePlane_dimension f.property) S
  intro p hp q hq hpq
  exact (native_framePlane_orthogonal_iff p.property q.property).mpr (orth hp hq hpq)

/-- Every exhaustive orthogonal decomposition into Albert closed planes has thirteen planes. -/
theorem native_completePlane_count {ι : Type*} [Fintype ι]
    (P : PlaneDecomposition NativeTraceless ι) :
    Fintype.card ι = 13 :=
  (orthogonalPlaneFamily_capacity nativeTraceless_finrank P.plane P.dimension
    P.pairwise_orthogonal).2.mp P.exhaustive

end
end ThirteenPlanes.JordanFrames
