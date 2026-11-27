module

public import ThirteenPlanes.AlbertGrading.Completion.Statements

@[expose] public section

/-! Frame planes of the native Albert algebra: the directions of the Jordan frame and closed-plane correspondence used by the completion,
proved directly (unbiased frames have orthogonal planes; a frame whose plane is orthogonal to that of
another frame is unbiased to it; a frame plane determines its frame as an unordered triple). -/

namespace ThirteenPlanes.AlbertGrading.CompletionO

open ThirteenPlanes
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- The centered idempotents of a frame lie in its plane. -/
theorem center_mem_framePlane {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (a : Fin 3) :
    nativeCenter (p a) ∈ nativeFramePlane p := by
  let u : Fin 3 → ℝ := Pi.single a 1
  have hu : ∑ b, u b = 1 := by simp [u]
  have hpoint : nativeFrameSynthesis p u = p a := by
    simp [nativeFrameSynthesis, u, Pi.single_apply]
  have hsum : (∑ b, (u b - (∑ k, u k) / 3)) = 0 := by
    rw [Finset.sum_sub_distrib, hu]
    norm_num
  obtain ⟨v, hv⟩ := nativeFrameEntries_surjective_of_zero_sum _ hsum
  refine ⟨v, Subtype.ext ?_⟩
  rw [nativeFrameChart_coe hp, nativeCenter_coe, hv, ← hpoint, nativeFrameSynthesis_centered hp]

/-- Unbiased frames have orthogonal planes. -/
theorem framePlanes_orthogonal {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (h : NativeUnbiased p q) :
    (nativeFramePlane p).IsOrtho (nativeFramePlane q) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
  change Glennie.inner (nativeFrameChart p u) (nativeFrameChart q v) = 0
  rw [nativeFrameChart_coe hp, nativeFrameChart_coe hq, nativeFrameSynthesis_inner]
  apply Finset.sum_eq_zero
  intro a _
  rw [nativeFrame_inner_synthesis]
  simp only [h a]
  rw [← Finset.sum_mul, nativeFrameEntries_sum, zero_mul, mul_zero]

theorem frame_point_decomposition {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (a : Fin 3) :
    p a = (nativeCenter (p a) : Glennie.Albert) + (1 / 3 : ℝ) • (1 : Glennie.Albert) := by
  rw [nativeCenter_coe, Glennie.traceless, hp.trace_one]
  abel

/-- A frame whose plane is orthogonal to the plane of another frame is unbiased to it. -/
theorem unbiased_of_framePlanes_orthogonal {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (h : (nativeFramePlane p).IsOrtho (nativeFramePlane q)) :
    NativeUnbiased p q := by
  intro a b
  have h0 := Submodule.isOrtho_iff_inner_eq.mp h _ (center_mem_framePlane hp a) _
    (center_mem_framePlane hq b)
  change Glennie.inner (nativeCenter (p a) : Glennie.Albert) (nativeCenter (q b)) = 0 at h0
  rw [frame_point_decomposition hp a, frame_point_decomposition hq b, Glennie.inner_add_left,
    Glennie.inner_add_right, Glennie.inner_add_right, Glennie.inner_smul_right,
    Glennie.inner_smul_left, Glennie.inner_smul_left, Glennie.inner_smul_right, h0,
    nativeInner_one_right, nativeInner_one_left, nativeInner_one_left, nativeTraceless_trace,
    nativeTraceless_trace, Glennie.trace_unit]
  norm_num

/-- Every idempotent of a frame whose plane lies in the plane of another frame is one of the
idempotents of that frame. -/
theorem frame_point_mem_of_framePlane_le {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (hle : nativeFramePlane q ≤ nativeFramePlane p) (b : Fin 3) :
    ∃ a, q b = p a := by
  obtain ⟨u, hu⟩ := hle (center_mem_framePlane hq b)
  have hu' := congrArg Subtype.val hu
  rw [nativeFrameChart_coe hp, nativeCenter_coe, Glennie.traceless, hq.trace_one] at hu'
  let k : Fin 3 → ℝ := fun a => nativeFrameEntries u a + 1 / 3
  have hk : q b = nativeFrameSynthesis p k := by
    have hk' : k = nativeFrameEntries u + fun _ => (1 / 3 : ℝ) := rfl
    rw [hk', map_add, nativeFrameSynthesis_const hp, hu']
    abel
  have hsq : nativeFrameSynthesis p (fun a => k a * k a) = nativeFrameSynthesis p k := by
    rw [← nativeFrameSynthesis_jordan hp, ← hk]
    exact hq.idempotent b
  have hidem (a : Fin 3) : k a * k a = k a := by
    have h := congrArg (Glennie.inner (p a)) hsq
    rwa [nativeFrame_analysis_synthesis hp, nativeFrame_analysis_synthesis hp] at h
  have htr : k 0 + k 1 + k 2 = 1 := by
    have h := hq.trace_one b
    rw [hk, nativeFrameSynthesis_trace hp, Fin.sum_univ_three] at h
    exact h
  have hk3 : q b = k 0 • p 0 + k 1 • p 1 + k 2 • p 2 := by
    rw [hk]
    change ∑ a, k a • p a = _
    rw [Fin.sum_univ_three]
  have bin (a : Fin 3) : k a = 0 ∨ k a = 1 := by
    have h := hidem a
    have : k a * (k a - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  rcases bin 0 with h0 | h0 <;> rcases bin 1 with h1 | h1 <;> rcases bin 2 with h2 | h2
  · exfalso; linarith
  · exact ⟨2, by rw [hk3, h0, h1, h2]; simp⟩
  · exact ⟨1, by rw [hk3, h0, h1, h2]; simp⟩
  · exfalso; linarith
  · exact ⟨0, by rw [hk3, h0, h1, h2]; simp⟩
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith

/-- Frames with the same plane are the same unordered triple. -/
theorem range_eq_of_framePlane_eq {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (h : nativeFramePlane q = nativeFramePlane p) :
    Set.range q = Set.range p := by
  apply Set.Subset.antisymm
  · rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := frame_point_mem_of_framePlane_le hp hq h.le b
    exact ⟨a, ha.symm⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := frame_point_mem_of_framePlane_le hq hp h.ge a
    exact ⟨b, hb.symm⟩

end

end ThirteenPlanes.AlbertGrading.CompletionO
