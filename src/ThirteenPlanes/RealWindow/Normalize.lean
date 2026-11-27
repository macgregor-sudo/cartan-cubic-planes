module

public import ThirteenPlanes.RealWindow.Slots
public import ThirteenPlanes.RealWindow.RealPoints
public import ThirteenPlanes.Qutrit.NativeData
public import ThirteenPlanes.Peirce.NativeFrameFormula

@[expose] public section

set_option backward.privateInPublic true

/-! Conjugate a closed real Cartan block in the native Albert algebra to the real matrix window. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open Peirce RoundCubics JordanFrames AlbertSequential AlbertSequential.NativeAnalysis

noncomputable section

private def blockJoin (U : Submodule ℝ NativeTraceless) : (U × ℝ) →ₗ[ℝ] Albert where
  toFun x := recoveredCoordinateEquiv.symm (((x.1 : NativeTraceless) : Glennie.Albert) +
    x.2 • (1 : Glennie.Albert))
  map_add' x y := by
    apply recoveredCoordinateEquiv.injective
    simp only [← map_add, LinearEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' r x := by
    apply recoveredCoordinateEquiv.injective
    rw [← map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change (r • ((x.1 : NativeTraceless) : Glennie.Albert) + (r * x.2) • (1 : Glennie.Albert)) =
      r • (((x.1 : NativeTraceless) : Glennie.Albert) + x.2 • (1 : Glennie.Albert))
    rw [smul_add, smul_smul]

private theorem blockJoin_image (U : Submodule ℝ NativeTraceless) (x : U × ℝ) :
    recoveredCoordinateEquiv (blockJoin U x) = ((x.1 : NativeTraceless) : Glennie.Albert) +
      x.2 • (1 : Glennie.Albert) := recoveredCoordinateEquiv.apply_symm_apply _

private theorem blockJoin_trace (U : Submodule ℝ NativeTraceless) (x : U × ℝ) :
    albertTrace (blockJoin U x) = 3 * x.2 := by
  rw [← recoveredCoordinateEquiv_trace, blockJoin_image, Glennie.trace_add, Glennie.trace_smul,
    nativeTraceless_trace, Glennie.trace_unit, zero_add, mul_comm]

private theorem blockJoin_injective (U : Submodule ℝ NativeTraceless) :
    Function.Injective (blockJoin U) := by
  intro x y he
  have h := congrArg albertTrace he
  rw [blockJoin_trace, blockJoin_trace] at h
  have h₂ : x.2 = y.2 := by linarith
  have h₁ := congrArg recoveredCoordinateEquiv he
  rw [blockJoin_image, blockJoin_image, h₂] at h₁
  exact Prod.ext (Subtype.ext (Subtype.ext (add_right_cancel h₁))) h₂

set_option maxHeartbeats 700000 in
private def blockUnital (U : Submodule ℝ NativeTraceless)
    (closed : IsClosedPiece nativeEqualCubic U) : NativeJordanSubalgebra where
  carrier := LinearMap.range (blockJoin U)
  unit_mem := by
    refine ⟨(0, 1), recoveredCoordinateEquiv.injective ?_⟩
    rw [blockJoin_image, recoveredCoordinateEquiv_unit]
    simp
  product_mem := by
    intro a ha b hb
    change a ∈ LinearMap.range (blockJoin U) at ha
    change b ∈ LinearMap.range (blockJoin U) at hb
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    let u : U := ⟨nativeEqualCubic.L (x.1 : NativeTraceless) (y.1 : NativeTraceless),
      closed x.1.property y.1.property⟩
    refine ⟨(u + x.2 • y.1 + y.2 • x.1, x.2 * y.2 + ⟪x.1, y.1⟫ / 3), ?_⟩
    apply recoveredCoordinateEquiv.injective
    rw [blockJoin_image, recoveredCoordinateEquiv_jordanMul, blockJoin_image, blockJoin_image]
    have hspl := native_jordan_split (x.1 : NativeTraceless) (y.1 : NativeTraceless)
    change Glennie.jordan (x.1 : NativeTraceless) (y.1 : NativeTraceless) =
      ((u : NativeTraceless) : Glennie.Albert) + (⟪x.1, y.1⟫ / 3) • (1 : Glennie.Albert) at hspl
    simp only [Submodule.coe_add, Submodule.coe_smul, Glennie.jordan_add_left, Glennie.jordan_add_right,
      Glennie.jordan_smul_left, Glennie.jordan_smul_right, Glennie.jordan_unit_left, Glennie.jordan_unit_right,
      hspl, smul_add, smul_smul, add_smul]
    module

private theorem blockUnital_membership (U : Submodule ℝ NativeTraceless)
    (closed : IsClosedPiece nativeEqualCubic U) (x : NativeTraceless) :
    recoveredCoordinateEquiv.symm x.val ∈ (blockUnital U closed).carrier ↔ x ∈ U := by
  constructor
  · rintro ⟨y, h⟩
    have htrace := congrArg albertTrace h
    rw [blockJoin_trace, ← recoveredCoordinateEquiv_trace, recoveredCoordinateEquiv.apply_symm_apply,
      nativeTraceless_trace] at htrace
    have hs : y.2 = 0 := by linarith
    have he := congrArg recoveredCoordinateEquiv h
    rw [blockJoin_image, recoveredCoordinateEquiv.apply_symm_apply, hs, zero_smul, add_zero] at he
    have hx : (y.1 : NativeTraceless) = x := Subtype.ext he
    exact hx ▸ y.1.property
  · intro hx
    refine ⟨(⟨x, hx⟩, 0), recoveredCoordinateEquiv.injective ?_⟩
    rw [blockJoin_image, recoveredCoordinateEquiv.apply_symm_apply]
    change x.val + (0 : ℝ) • (1 : Glennie.Albert) = x.val
    simp

private abbrev s : ℝ := Real.sqrt 6

private theorem sqrt6_pos : 0 < s := Real.sqrt_pos.mpr (by norm_num)

private theorem atomOfIdempotent {U : Submodule ℝ NativeTraceless}
    (x : U) (hxnorm : ‖x‖ = 1)
    (hxsq : s • nativeCenteredJordan (x : NativeTraceless) (x : NativeTraceless) = (x : NativeTraceless)) :
    IsAtom (recoveredCoordinateEquiv.symm ((1 / 3 : ℝ) •
      ((1 : Glennie.Albert) + s • ((x : NativeTraceless) : Glennie.Albert)))) := by
  let v : NativeTraceless := x
  let w : Glennie.Albert := v
  let f : Glennie.Albert := (1 / 3 : ℝ) • ((1 : Glennie.Albert) + s • w)
  have hv : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, show ‖v‖ = 1 from hxnorm, one_pow]
  have hcen : nativeCenteredJordan v v = s⁻¹ • v := by
    calc
      _ = s⁻¹ • (s • nativeCenteredJordan v v) := by
        rw [smul_smul, inv_mul_cancel₀ sqrt6_pos.ne', one_smul]
      _ = _ := congrArg (s⁻¹ • ·) hxsq
  have hj := native_jordan_split v v
  change Glennie.jordan w w = (nativeCenteredJordan v v : Glennie.Albert) +
    (⟪v, v⟫ / 3) • (1 : Glennie.Albert) at hj
  rw [hcen, hv, Submodule.coe_smul] at hj
  have hs : s ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ sqrt6_pos.ne'
  have hsi' : s ^ 2 * s⁻¹ = s := by rw [pow_two, mul_assoc, hsi, mul_one]
  refine ⟨recoveredCoordinateEquiv.injective ?_, ?_⟩
  · change recoveredCoordinateEquiv (jordanMul (recoveredCoordinateEquiv.symm f)
      (recoveredCoordinateEquiv.symm f)) = recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm f)
    rw [recoveredCoordinateEquiv_jordanMul, recoveredCoordinateEquiv.apply_symm_apply]
    dsimp only [f]
    simp only [Glennie.jordan_add_left, Glennie.jordan_add_right, Glennie.jordan_smul_left,
      Glennie.jordan_smul_right, Glennie.jordan_unit_left, Glennie.jordan_unit_right, hj,
      smul_add, smul_smul]
    match_scalars
    · linear_combination hs / 27
    · linear_combination hsi' / 9
  · rw [← recoveredCoordinateEquiv_trace, recoveredCoordinateEquiv.apply_symm_apply]
    rw [Glennie.trace_smul, Glennie.trace_add, Glennie.trace_unit, Glennie.trace_smul]
    change (1 / 3 : ℝ) * (3 + s * Glennie.trace v.val) = 1
    rw [nativeTraceless_trace]
    norm_num

private def recoveredFrame (p : Fin 3 → Glennie.Albert) (hp : Glennie.Frame p) : NativeJordanFrame where
  atom i := recoveredCoordinateEquiv.symm (p i)
  atoms i := by
    refine ⟨recoveredCoordinateEquiv.injective ?_, ?_⟩
    · simpa only [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply] using hp.idempotent i
    · rw [← recoveredCoordinateEquiv_trace, LinearEquiv.apply_symm_apply]
      exact hp.trace_one i
  orthogonal i j hij := by
    apply recoveredCoordinateEquiv.injective
    simpa only [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply, map_zero] using
      hp.orthogonal i j hij
  sum_unit := by
    apply recoveredCoordinateEquiv.injective
    rw [map_sum, recoveredCoordinateEquiv_unit]
    simp only [LinearEquiv.apply_symm_apply, Fin.sum_univ_three]
    exact hp.sum_unit

set_option maxHeartbeats 1400000 in
/-- The actual compact Albert automorphism taking a closed real Cartan block to the trace-zero
part of the standard real symmetric matrix window. -/
theorem nativeRealBlock_to_standard {U : Submodule ℝ NativeTraceless}
    (closed : IsClosedPiece nativeEqualCubic U)
    (I : U ≃ₗᵢ[ℝ] RealTracelessSymmetric3)
    (hI : nativeEqualCubic.pullback (W := ↥U) U.subtype =
      s⁻¹ • realCartanCubic.pullback (W := ↥U) I.toLinearMap) :
    ∃ g : NativeAlbertAutomorphism, ∀ x : NativeTraceless,
      g.linearEquiv (recoveredCoordinateEquiv.symm x.val) ∈ (H3Subalgebra .R).carrier ↔ x ∈ U := by
  let B := blockUnital U closed
  have dimU : Module.finrank ℝ U = 5 := by
    rw [I.toLinearEquiv.finrank_eq, ← realCartanEquiv.finrank_eq]
    simp [Module.finrank_prod]
  have dimB : Module.finrank ℝ B.carrier = 6 := by
    change Module.finrank ℝ (LinearMap.range (blockJoin U)) = 6
    rw [← (LinearEquiv.ofInjective (blockJoin U) (blockJoin_injective U)).finrank_eq,
      Module.finrank_prod, dimU, Module.finrank_self]
  let k := s • nativeEqualCubic.pullback (W := ↥U) U.subtype
  have hk : k = realCartanCubic.pullback I.toLinearMap := by
    dsimp only [k]
    rw [hI, smul_smul, mul_inv_cancel₀ sqrt6_pos.ne', one_smul]
  let inc : U →ₗᵢ[ℝ] NativeTraceless := U.subtypeₗᵢ
  have inter (x y : U) : inc (k.L x y) = s • nativeCenteredJordan (inc x) (inc y) := by
    have hc := closedSubspace_restriction_product closed x y
    change ((s • (nativeEqualCubic.pullback (W := ↥U) U.subtype)).L x y : NativeTraceless) = _
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, hc]
    rfl
  obtain ⟨a, b, ha, hsum, hb, ortho⟩ := realCartan_has_flat_frame
  let aU (i : Fin 3) : U := I.symm (a i)
  let bU := I.symm b
  have idemp (x : RealTracelessSymmetric3) (hx : IsUnitIdempotent realCartanCubic x) :
      IsUnitIdempotent k (I.symm x) := by
    refine ⟨(I.symm.norm_map x).trans hx.norm_eq_one, I.injective ?_⟩
    rw [pullback_intertwines_product (h := k) (k := realCartanCubic) I hk,
      I.apply_symm_apply, hx.square_eq_self]
  have sa : ∑ i, aU i = 0 := by
    change (∑ i, I.symm.toLinearMap (a i)) = _
    rw [← map_sum I.symm.toLinearMap, hsum, map_zero]
  let point (x : U) : Glennie.Albert :=
    (1 / 3 : ℝ) • ((1 : Glennie.Albert) + s • ((inc x : NativeTraceless) : Glennie.Albert))
  have hframe : Glennie.Frame (fun i => point (aU i)) :=
    nativeFrame_of_three_unit_idempotents_of_intertwines (h := k) inc inter aU (fun i => idemp _ (ha i)) sa
  let p (x : U) : Albert := recoveredCoordinateEquiv.symm (point x)
  let F := recoveredFrame (fun i => point (aU i)) hframe
  have pmem (x : U) : p x ∈ B.carrier := by
    refine ⟨((s / 3) • x, 1 / 3), recoveredCoordinateEquiv.injective ?_⟩
    rw [blockJoin_image, show recoveredCoordinateEquiv (p x) = point x from
      recoveredCoordinateEquiv.apply_symm_apply _]
    change ((s / 3) • ((x : NativeTraceless) : Glennie.Albert)) + (1 / 3 : ℝ) • (1 : Glennie.Albert) =
      (1 / 3 : ℝ) • ((1 : Glennie.Albert) + s • ((x : NativeTraceless) : Glennie.Albert))
    module
  have pb_atom : IsAtom (p bU) := by
    have hbU := idemp b hb
    apply atomOfIdempotent bU hbU.norm_eq_one
    change s • nativeCenteredJordan (inc bU) (inc bU) = inc bU
    rw [← inter bU bU, hbU.square_eq_self]
  have sourceOrth (i : Fin 3) : ⟪aU i, bU⟫ = 0 := by
    have hi := norm_add_sq_real (I.symm (a i)) (I.symm b)
    have hAdd : I.symm (a i + b) = I.symm (a i) + I.symm b :=
      I.symm.toLinearMap.map_add _ _
    rw [← hAdd, I.symm.norm_map, I.symm.norm_map, I.symm.norm_map] at hi
    have hj := norm_add_sq_real (a i) b
    rw [ortho i] at hj
    change ⟪I.symm (a i), I.symm b⟫ = 0
    linarith only [hi, hj]
  have pb_balanced (i : Fin 3) : AlbertSequential.tracePairing (F.atom i) (p bU) = 1 / 3 := by
    rw [← recoveredCoordinateEquiv_tracePairing]
    change Glennie.inner (point (aU i)) (point bU) = 1 / 3
    have htr (x : U) : Glennie.inner 1 ((x : NativeTraceless) : Glennie.Albert) = 0 := by
      rw [nativeInner_one_left, nativeTraceless_trace]
    have htr' (x : U) : Glennie.inner ((x : NativeTraceless) : Glennie.Albert) 1 = 0 :=
      (Glennie.inner_comm _ _).trans (htr x)
    have ho := sourceOrth i
    change Glennie.inner (((aU i : U) : NativeTraceless) : Glennie.Albert)
      ((bU : NativeTraceless) : Glennie.Albert) = 0 at ho
    change Glennie.inner
        ((1 / 3 : ℝ) • ((1 : Glennie.Albert) + s • (((aU i : U) : NativeTraceless) : Glennie.Albert)))
        ((1 / 3 : ℝ) • ((1 : Glennie.Albert) + s • ((bU : NativeTraceless) : Glennie.Albert))) = _
    simp only [Glennie.inner_smul_left, Glennie.inner_smul_right, Glennie.inner_add_left,
      Glennie.inner_add_right, htr, htr', ho, nativeInner_one_left, Glennie.trace_unit]
    ring
  obtain ⟨g, hg⟩ := nativeFramedRealWindow_to_standard B dimB F (fun i => pmem (aU i))
    (p bU) pb_atom (pmem bU) pb_balanced
  exact ⟨g, fun x => (hg _).trans (blockUnital_membership U closed x)⟩

end

end ThirteenPlanes.ClosedBlocks
