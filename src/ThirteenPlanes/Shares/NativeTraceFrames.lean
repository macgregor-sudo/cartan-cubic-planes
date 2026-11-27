module

public import ThirteenPlanes.Shares.TraceFrames
public import ThirteenPlanes.NativeFrames

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace

noncomputable section

abbrev nativeTraceInclusion : NativeTraceless →ₗᵢ[ℝ] Glennie.Albert :=
  Glennie.traceLinear.ker.subtypeₗᵢ

def nativeFullCubic : SymmetricCubic Glennie.Albert :=
  SymmetricCubic.ofProduct Glennie.jordanLinear Glennie.jordan_comm (by
    intro x y z
    change Glennie.inner (Glennie.jordan x y) z = Glennie.inner (Glennie.jordan x z) y
    rw [Glennie.inner_jordan_associative, Glennie.inner_jordan_associative, Glennie.jordan_comm y z])

private def nativeCenteredPoint {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (a : Fin 3) : nativeFramePlane p := by
  refine ⟨nativeCenter (p a), ?_⟩
  let u : Fin 3 → ℝ := Pi.single a 1
  have hu : ∑ b, u b = 1 := by simp [u]
  have hpoint : nativeFrameSynthesis p u = p a := by simp [nativeFrameSynthesis, u, Pi.single_apply]
  have hsum : (∑ b, (u b - (∑ k, u k) / 3)) = 0 := by
    rw [Finset.sum_sub_distrib, hu]
    norm_num
  obtain ⟨v, hv⟩ := nativeFrameEntries_surjective_of_zero_sum _ hsum
  refine ⟨v, Subtype.ext ?_⟩
  rw [nativeFrameChart_coe hp, nativeCenter_coe, hv, ← hpoint, nativeFrameSynthesis_centered hp]

private theorem nativeCenteredPoint_span {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    Submodule.span ℝ (Set.range (nativeCenteredPoint hp)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨u, hu⟩ := z.property
  have hrep : z = ∑ a, nativeFrameEntries u a • nativeCenteredPoint hp a := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (z : NativeTraceless) = ∑ a, nativeFrameEntries u a • nativeCenter (p a)
    rw [← hu]
    change nativeCenter (∑ a, nativeFrameEntries u a • p a) = _
    simp only [map_sum, map_smul]
  rw [hrep]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

def nativeCenteredTraceFrame {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (S : Submodule ℝ NativeTraceless) (hS : S = nativeFramePlane p) :
    CenteredTraceFrame nativeTraceInclusion (1 : Glennie.Albert) S := by
  subst S
  refine ⟨p, orthonormal_iff_ite.mpr ?_, ?_, nativeCenteredPoint hp, ?_, nativeCenteredPoint_span hp⟩
  · intro a b
    exact nativeFrame_gram hp a b
  · simpa only [Fin.sum_univ_three] using hp.sum_unit
  · intro a
    change Glennie.traceless (p a) = p a - (1 / 3 : ℝ) • (1 : Glennie.Albert)
    simp only [Glennie.traceless, hp.trace_one]


theorem nativeFullCubic_apply (x y z : Glennie.Albert) :
    nativeFullCubic.apply x y z = Glennie.trace (Glennie.jordan (Glennie.jordan x y) z) := rfl

/-- The literal trace-of-three-points formula for arbitrary standalone compact-Albert frame planes. -/
theorem native_shareOfThreePlanes_eq_frame_trace
    {p q r : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (hq : Glennie.Frame q)
    (hr : Glennie.Frame r) (orth : (nativeFramePlane p).IsOrtho (nativeFramePlane q))
    (orthW : (nativeFramePlane p).IsOrtho (nativeFramePlane r))
    (orth'W : (nativeFramePlane q).IsOrtho (nativeFramePlane r)) :
    shareOfThreePlanes nativeEqualCubic (nativeFramePlane p) (nativeFramePlane q) (nativeFramePlane r) =
      6 * ∑ a, ∑ b, ∑ d,
        (Glennie.trace (Glennie.jordan (Glennie.jordan (p a) (q b)) (r d)) - 1 / 9) ^ 2 := by
  have round : IsRound nativeEqualCubic (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [nativeEqualCubic_squareLaw x]
    ring
  have unit (x : Glennie.Albert) : nativeFullCubic.L 1 x = x := Glennie.jordan_unit_left x
  have metric (x y z : NativeTraceless) :
      nativeEqualCubic.apply x y z =
        nativeFullCubic.apply (nativeTraceInclusion x) (nativeTraceInclusion y) (nativeTraceInclusion z) := by
    change Glennie.inner (Glennie.traceless (Glennie.jordan x y)) z =
      Glennie.inner (Glennie.jordan x y) z
    exact nativeInner_center_left _ _
  let F := nativeCenteredTraceFrame hp _ rfl
  let G := nativeCenteredTraceFrame hq _ rfl
  let H := nativeCenteredTraceFrame hr _ rfl
  have eq := shareOfThreePlanes_eq_centered_frame_trace (h := nativeEqualCubic)
    (J := nativeTraceInclusion) round orth orthW orth'W
    (by intro x y hx hy; exact nativeFramePlane_closed hp hx hy)
    (by intro x y hx hy; exact nativeFramePlane_closed hq hx hy)
    (nativeFramePlane_dimension hp) nativeFullCubic unit metric F G H
  rw [eq]
  have hf : F.point = p := rfl
  have hg : G.point = q := rfl
  have hh : H.point = r := rfl
  simp only [hf, hg, hh, nativeFullCubic_apply]

end
end ThirteenPlanes.RoundCubics
