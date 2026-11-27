/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.NativeFrames

@[expose] public section

/-! The concrete native Albert input to the common plane contraction proof. -/

noncomputable section

namespace ThirteenPlanes

open scoped BigOperators

theorem TightNativeCode.planes_exhaustive (c : TightNativeCode) :
    (⨆ f : Fin 13, nativeFramePlane (c.point f)) = ⊤ := by
  have h : iSupIndep (fun f => nativeFramePlane (c.point f)) := by
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hsum f hf
    have hh := congrArg (fun z : NativeTraceless => inner ℝ (v f) z) hsum
    simp only [inner_sum, inner_zero_right] at hh
    rw [Finset.sum_eq_single f] at hh
    · exact inner_self_eq_zero.mp hh
    · intro g hg hgf
      exact (c.planes_orthogonal hgf.symm).inner_eq (hv f hf) (hv g hg)
    · simp [hf]
  apply Submodule.eq_top_of_finrank_eq
  rw [Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj h.dfinsupp_lsum_injective]
  change Module.finrank ℝ (DirectSum (Fin 13) (fun i => ↥(nativeFramePlane (c.point i)))) = _
  rw [Module.finrank_directSum, nativeTraceless_finrank]
  simp [nativeFramePlane_dimension (c.frame _)]

abbrev TightNativeCode.decomposition (c : TightNativeCode) : PlaneDecomposition NativeTraceless (Fin 13) where
  plane f := nativeFramePlane (c.point f)
  dimension f := nativeFramePlane_dimension (c.frame f)
  pairwise_orthogonal := c.planes_orthogonal
  exhaustive := c.planes_exhaustive

def TightNativeCode.cubicPair (c : TightNativeCode) : CubicPair NativeTraceless :=
  let diagonal := ∑ f : Fin 13, nativeEqualCubic.pullback (c.decomposition.proj f)
  ⟨diagonal, nativeEqualCubic - diagonal⟩

@[simp] theorem TightNativeCode.interaction_one (c : TightNativeCode) :
    interactionCubic c.cubicPair 1 = nativeEqualCubic := by
  rw [interactionCubic, coupling_apply]
  simp only [one_smul]
  unfold TightNativeCode.cubicPair
  dsimp only
  rw [add_comm]
  exact sub_add_cancel nativeEqualCubic _

theorem TightNativeCode.squareLaw (c : TightNativeCode) :
    HasSquareLaw (interactionCubic c.cubicPair 1) := by
  rw [c.interaction_one]
  exact nativeEqualCubic_squareLaw

def nativeFrameChartEquiv {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] nativeFramePlane p :=
  LinearEquiv.ofInjective (nativeFrameChart p) (nativeFrameChart_injective hp)

theorem nativeFrameChartEquiv_symm_entry {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (x : nativeFramePlane p) (b : Fin 2) :
    (nativeFrameChartEquiv hp).symm x b = Glennie.inner (p b.castSucc) x := by
  have h := congrArg (fun z : nativeFramePlane p => Glennie.inner (p b.castSucc) z)
    ((nativeFrameChartEquiv hp).apply_symm_apply x)
  change Glennie.inner (p b.castSucc) (nativeFrameChart p ((nativeFrameChartEquiv hp).symm x)) =
    _ at h
  rw [nativeFrameChart_coe hp, nativeFrame_analysis_synthesis hp] at h
  fin_cases b <;> exact h

theorem nativeFrame_analysis_sum {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (x : Glennie.Albert) : ∑ b, Glennie.inner (p b) x = Glennie.trace x := by
  calc
    _ = Glennie.inner (nativeFrameSynthesis p (fun _ => 1)) x := by
      rw [nativeFrameSynthesis_inner]; simp
    _ = _ := by rw [nativeFrameSynthesis_const hp, one_smul, nativeInner_one_left]

theorem nativeFrame_restriction_L (c : TightNativeCode) (f : Fin 13) (x y : c.decomposition.plane f) :
    ((c.decomposition.restriction f nativeEqualCubic).L x y : NativeTraceless) =
      nativeCenteredJordan x y := by
  let j : c.decomposition.plane f :=
    ⟨nativeCenteredJordan x y, nativeFramePlane_closed (c.frame f) x.property y.property⟩
  suffices h : (c.decomposition.restriction f nativeEqualCubic).L x y = j by
    exact congrArg Subtype.val h
  apply ext_inner_right ℝ
  intro z
  change (c.decomposition.restriction f nativeEqualCubic).apply x y z = _
  rw [PlaneDecomposition.restriction_apply]
  rfl

theorem nativeFrame_synthesis_analysis {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (x : nativeFramePlane p) :
    (x : Glennie.Albert) = nativeFrameSynthesis p (fun b => Glennie.inner (p b) x) := by
  obtain ⟨u, hu⟩ := x.property
  have hx : nativeFrameSynthesis p (nativeFrameEntries u) = (x : Glennie.Albert) :=
    (nativeFrameChart_coe hp u).symm.trans (congrArg Subtype.val hu)
  calc
    _ = nativeFrameSynthesis p (nativeFrameEntries u) := hx.symm
    _ = _ := by
      congr 1
      funext b
      rw [← hx, nativeFrame_analysis_synthesis hp]

set_option maxHeartbeats 800000 in
theorem TightNativeCode.plane_traceFree (c : TightNativeCode) (i : Fin 13) :
    (c.decomposition.restriction i nativeEqualCubic).TraceFree := by
  intro x
  let r := fun b => Glennie.inner (c.point i b) (x : Glennie.Albert)
  let e := nativeFrameChartEquiv (c.frame i)
  let f : Module.End ℝ (c.decomposition.plane i) := (c.decomposition.restriction i nativeEqualCubic).L x
  let g := e.symm.conj f
  have hr : r 2 = -(r 0 + r 1) := by
    have h : ∑ b, r b = 0 := (nativeFrame_analysis_sum (c.frame i) x).trans (nativeTraceless_trace _)
    rw [Fin.sum_univ_three] at h
    linarith
  have hx : (x : Glennie.Albert) = nativeFrameSynthesis (c.point i) r :=
    nativeFrame_synthesis_analysis (c.frame i) x
  have hcoeff (u : Fin 2 → ℝ) (b : Fin 2) :
      g u b = r b.castSucc * nativeFrameEntries u b.castSucc -
        (∑ a, r a * nativeFrameEntries u a) / 3 := by
    let y := e u
    change (nativeFrameChartEquiv (c.frame i)).symm (f y) b = _
    rw [nativeFrameChartEquiv_symm_entry]
    change Glennie.inner (c.point i b.castSucc)
      ((c.decomposition.restriction i nativeEqualCubic).L x y : NativeTraceless) = _
    rw [nativeFrame_restriction_L, nativeCenteredJordan_apply, nativeCenter_coe]
    have hy : (y : Glennie.Albert) = nativeFrameSynthesis (c.point i) (nativeFrameEntries u) :=
      nativeFrameChart_coe (c.frame i) u
    rw [hx, hy, nativeFrameSynthesis_jordan (c.frame i),
      nativeFrameSynthesis_centered (c.frame i), nativeFrame_analysis_synthesis (c.frame i)]
  change LinearMap.trace ℝ (c.decomposition.plane i) f = 0
  rw [← LinearMap.trace_conj' f e.symm]
  change LinearMap.trace ℝ (Fin 2 → ℝ) g = 0
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 2))]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, LinearMap.toMatrix_apply,
    Pi.basisFun_repr, Pi.basisFun_apply, hcoeff]
  norm_num [nativeFrameEntries, Fin.sum_univ_three, Pi.single_apply, hr]
  ring

theorem TightNativeCode.planeData (c : TightNativeCode) :
    HasPlaneData c.cubicPair c.decomposition where
  diagonal_eq := by simp only [c.interaction_one]; rfl
  traceFree i := by rw [c.interaction_one]; exact c.plane_traceFree i
  repeatedPlane f x y z := by
    rw [c.interaction_one]
    change inner ℝ (nativeCenteredJordan x y) z = 0
    exact z.property _ (nativeFramePlane_closed (c.frame f) x.property y.property)

end ThirteenPlanes
