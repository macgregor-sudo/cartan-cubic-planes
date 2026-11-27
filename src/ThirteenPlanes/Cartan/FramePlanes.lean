module

public import ThirteenPlanes.BinaryPlane
public import ThirteenPlanes.Cartan.JordanOperators
public import ThirteenPlanes.NativeFrames
public import Glennie.Diagonalization
public import NativeJordanIdentity

@[expose] public section

set_option backward.privateInPublic true

/-! Frame extraction from the compact Albert spectral theorem and round binary geometry. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace
open RoundCubics

noncomputable section

/-- An individual spectral theorem suffices to recover the entire closed binary plane.
One unit member with vanishing cubic and its orthogonal nonzero square span it. -/
theorem closedTwoPlane_eq_spectralPlane
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (h : SymmetricCubic V) {c : ℝ} (round : IsRound h c)
    {F : Type*} (planes : F → Submodule ℝ V)
    (cover : ∀ x : V, ∃ f : F, x ∈ planes f)
    (dim : ∀ f, Module.finrank ℝ (planes f) = 2)
    (closed : ∀ f, IsClosedPiece h (planes f))
    (U : Submodule ℝ V) (dU : Module.finrank ℝ U = 2) (cU : IsClosedPiece h U) :
    ∃ f, U = planes f := by
  let hU := h.pullback U.subtype
  have hL (x y : U) : hU.L x y = ⟨h.L x.val y.val, cU x.property y.property⟩ := by
    apply ext_inner_right ℝ
    intro z
    change hU.apply x y z = h.apply x.val y.val z.val
    rw [SymmetricCubic.pullback_apply]
    rfl
  have roundU : IsRound hU c := by
    refine ⟨round.positive, fun x => ?_⟩
    simp only [SymmetricCubic.squareMap, hL]
    exact round.square_norm x.val
  obtain ⟨_, z, hz⟩ := binaryPlaneNormalForm roundU dU
  let u : U := z.symm Complex.I
  let x : V := u.val
  have hx : ‖x‖ = 1 := by
    change ‖z.symm Complex.I‖ = 1
    rw [z.symm.norm_map, Complex.norm_I]
  have hi : (Complex.I ^ 3).re = 0 := by
    rw [pow_succ, pow_two, Complex.I_mul_I, neg_one_mul, Complex.neg_re, Complex.I_re, neg_zero]
  have hzero : h.apply x x x = 0 := by
    have he := hz u
    rw [show z u = Complex.I from z.apply_symm_apply _, hi, mul_zero] at he
    change h.apply u.val u.val u.val = 0
    simpa only [hU, SymmetricCubic.pullback_apply, Submodule.subtype_apply] using he
  let y := h.L x x
  have hyU : y ∈ U := cU u.property u.property
  have hy0 : y ≠ 0 := by
    intro hn
    have he := round.square_norm x
    change ‖y‖ ^ 2 = c * ‖x‖ ^ 4 at he
    rw [hn, hx, norm_zero] at he
    norm_num at he
    exact round.positive.ne' he.symm
  let v : U := ⟨‖y‖⁻¹ • y, U.smul_mem _ hyU⟩
  have hv : ‖v‖ = 1 := by
    change ‖‖y‖⁻¹ • y‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
  have huv : ⟪u,v⟫ = 0 := by
    change inner ℝ x (‖y‖⁻¹ • y) = 0
    have hxy : inner ℝ x y = 0 := (real_inner_comm y x).trans hzero
    rw [real_inner_smul_right, hxy, mul_zero]
  let b : Fin 2 → U := ![u, v]
  have hb : Orthonormal ℝ b := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · change inner ℝ u u = 1
      rw [real_inner_self_eq_norm_sq, show ‖u‖ = 1 from hx, one_pow]
    · exact huv
    · exact (real_inner_comm u v).trans huv
    · change inner ℝ v v = 1
      rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ :=
    hb.linearIndependent.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, dU])
  obtain ⟨f, hf⟩ := cover x
  have hyf : y ∈ planes f := closed f hf hf
  have hincl : Submodule.span ℝ (Set.range b) ≤ (planes f).comap U.subtype := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hf
    · exact (planes f).smul_mem _ hyf
  have hle : U ≤ planes f := by
    intro w hw
    have hm : (⟨w, hw⟩ : U) ∈ Submodule.span ℝ (Set.range b) := by rw [hspan]; trivial
    exact hincl hm
  exact ⟨f, Submodule.eq_of_le_of_finrank_eq hle (dU.trans (dim f).symm)⟩

private theorem nativeJordanIdentity (x y : Glennie.Albert) :
    Glennie.jordan x (Glennie.jordan (Glennie.jordan x x) y) =
      Glennie.jordan (Glennie.jordan x x) (Glennie.jordan x y) := by
  let f := AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv
  have h := congrArg f
    (AlbertSequential.NativeAnalysis.jordan_identity (f.symm x) (f.symm y)).symm
  simp only [f, AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv_jordanMul,
    LinearEquiv.apply_symm_apply] at h
  rw [Glennie.jordan_comm (Glennie.jordan x x) y,
    Glennie.jordan_comm (Glennie.jordan x x) (Glennie.jordan x y)]
  exact h

/-- Actual native compact Albert unital multiplication and its trace metric. -/
def albertJordan : TraceJordanData Glennie.Albert where
  L := Glennie.jordanLinear
  unit := 1
  unit_left := Glennie.jordan_unit_left
  unit_trace := by rw [Glennie.hilbert_inner_eq_native, nativeInner_one_left, Glennie.trace_unit]
  comm := Glennie.jordan_comm
  assoc_inner x y z := by
    simp only [Glennie.jordanLinear_apply, Glennie.hilbert_inner_eq_native]
    rw [Glennie.jordan_comm x y, Glennie.inner_jordan_associative]
  jordan x := by
    unfold Commute SemiconjBy
    apply LinearMap.ext
    intro y
    simp only [mul_apply_eq_comp, Glennie.jordanLinear_apply]
    exact nativeJordanIdentity x y

@[simp] theorem albertJordan_trace (x : Glennie.Albert) : albertJordan.trace x = Glennie.trace x := by
  change inner ℝ (1 : Glennie.Albert) x = _
  rw [Glennie.hilbert_inner_eq_native, nativeInner_one_left]

theorem albertJordan_traceFree_eq : albertJordan.traceFree = Glennie.traceLinear.ker := by
  ext x
  change albertJordan.trace x = 0 ↔ Glennie.trace x = 0
  rw [albertJordan_trace]

private theorem nativeSpectral_cover (x : NativeTraceless) :
    ∃ f : {p : Fin 3 → Glennie.Albert // Glennie.Frame p}, x ∈ nativeFramePlane f.val := by
  obtain ⟨p, a, hf, hA⟩ := Glennie.compact_spectral_decomposition x.val
  have ha : (∑ i, a i) = 0 := by
    have htrace := nativeFrameSynthesis_trace hf a
    change Glennie.trace (∑ i, a i • p i) = _ at htrace
    rw [← hA, nativeTraceless_trace] at htrace
    exact htrace.symm
  obtain ⟨v, hv⟩ := nativeFrameEntries_surjective_of_zero_sum a ha
  refine ⟨⟨p, hf⟩, ⟨v, Subtype.ext ?_⟩⟩
  rw [nativeFrameChart_coe hf, hv]
  exact hA.symm

/-- A closed native Albert plane is the plane of a genuine native Jordan frame. -/
theorem nativeClosedPlane_has_frame (U : Submodule ℝ NativeTraceless)
    (dim : Module.finrank ℝ U = 2) (closed : IsClosedPiece nativeEqualCubic U) :
    ∃ p : Fin 3 → Glennie.Albert, Glennie.Frame p ∧ U = nativeFramePlane p := by
  have hround : IsRound nativeEqualCubic (1 / 6 : ℝ) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [nativeEqualCubic_squareLaw x]
    ring
  obtain ⟨f, hf⟩ := closedTwoPlane_eq_spectralPlane nativeEqualCubic hround
    (fun f : {p : Fin 3 → Glennie.Albert // Glennie.Frame p} => nativeFramePlane f.val)
    nativeSpectral_cover (fun f => nativeFramePlane_dimension f.property)
    (fun f _ _ hx hy => nativeFramePlane_closed f.property hx hy) U dim closed
  exact ⟨f.val, f.property, hf⟩

end

end ThirteenPlanes.Cartan
