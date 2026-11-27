module

public import ThirteenPlanes.AlbertGrading.Recognition.CoreMain
public import ThirteenPlanes.Shares.ThirteenIncidence
public import ThirteenPlanes.Graded.Incidence
public import ThirteenPlanes.NativeTits

@[expose] public section

/-!
# Transport of a sparsest native system to `J_T`

The accepted isomorphism `nativeCompactTitsEquiv : 𝔸 ≃ J_T` (product, trace and unit preserving;
the quoted theorem of Tits in the paper) carries a thirteen-plane system with 52 positive shares
to a `TitsSystem`. The quartets come from the thirteen-plane support and incidence theorem
(`thirteenPlane_shareSupport_and_incidence`) and the equality case of the plane-share sum rule.
-/

open scoped Matrix BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits RoundCubics

/-- The frames of a native system, in `J_T`. -/
def toTits (c : TightNativeCode) : Fin 13 → ZMod 3 → CompactTits :=
  fun i a => nativeCompactTitsEquiv (c.point i a)

theorem toTits_frame (c : TightNativeCode) (i : Fin 13) : IsTitsFrame (toTits c i) := by
  have hF := c.frame i
  have hid : ∀ a : ZMod 3, Glennie.jordan (c.point i a) (c.point i a) = c.point i a :=
    fun a => hF.idempotent a
  have hor : ∀ a b : ZMod 3, a ≠ b → Glennie.jordan (c.point i a) (c.point i b) = 0 :=
    fun a b h => hF.orthogonal a b h
  have htr : ∀ a : ZMod 3, Glennie.trace (c.point i a) = 1 := fun a => hF.trace_one a
  have hsum : c.point i (0 : ZMod 3) + c.point i (1 : ZMod 3) + c.point i (2 : ZMod 3) = 1 :=
    hF.sum_unit
  refine ⟨fun a b => ?_, fun a => ?_, ?_⟩
  · simp only [toTits, ← nativeCompactTitsEquiv_product]
    by_cases h : a = b
    · subst h; rw [hid, if_pos rfl]
    · rw [hor a b h, if_neg h, map_zero]
  · rw [toTits, nativeCompactTitsEquiv_trace]; exact htr a
  · rw [sum_zmod3]
    simp only [toTits, ← map_add]
    rw [hsum, nativeCompactTitsEquiv_one]

theorem nativeEqualCubic_L_coe' (x y : NativeTraceless) :
    ((nativeEqualCubic.L x y : NativeTraceless) : Glennie.Albert) =
      Glennie.jordan x y - (Glennie.trace (Glennie.jordan x y) / 3) • (1 : Glennie.Albert) := rfl

theorem framePlane_to_tits {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) {x : NativeTraceless}
    (hx : x ∈ nativeFramePlane p) :
    nativeCompactTitsEquiv (x : Glennie.Albert) ∈
      titsFramePlane (fun a : ZMod 3 => nativeCompactTitsEquiv (p a)) := by
  obtain ⟨u, rfl⟩ := hx
  rw [nativeFrameChart_coe hp]
  have hs := nativeFrameEntries_sum u
  have e : nativeCompactTitsEquiv (nativeFrameSynthesis p (nativeFrameEntries u)) =
      ∑ b : Fin 3, nativeFrameEntries u b •
        (nativeCompactTitsEquiv (p b) - (1 / 3 : ℝ) • CompactTits.one) := by
    change nativeCompactTitsEquiv (∑ b, nativeFrameEntries u b • p b) = _
    simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs,
      zero_smul, sub_zero]
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem center_mem_framePlane {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (a : Fin 3) :
    nativeCenter (p a) ∈ nativeFramePlane p := by
  let e : Fin 3 → ℝ := fun b => (if b = a then 1 else 0) - 1 / 3
  have hsum : ∑ b, e b = 0 := by
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨u, hu⟩ := nativeFrameEntries_surjective_of_zero_sum e hsum
  refine ⟨u, Subtype.ext ?_⟩
  rw [nativeFrameChart_coe hp, hu, nativeCenter_coe, Glennie.traceless, hp.trace_one]
  change ∑ b, e b • p b = _
  have h1 : ∑ b, e b • p b = p a - (1 / 3 : ℝ) • ∑ b, p b := by
    simp only [e, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]
  rw [h1, Fin.sum_univ_three, hp.sum_unit]

/-- A native system with 52 positive shares becomes a `TitsSystem`. -/
theorem toTits_system (c : TightNativeCode)
    (h52 : (positivePlaneTriples nativeEqualCubic c.decomposition).card = 52) :
    TitsSystem (toTits c) := by
  have round := Graded.nativeRound
  have closed : IsClosedPlaneSystem nativeEqualCubic c.decomposition := by
    intro i x y hx hy
    change nativeCenteredJordan x y ∈ nativeFramePlane (c.point i)
    exact nativeFramePlane_closed (c.frame i) hx hy
  have hthm := thirteenPlane_shareSupport_and_incidence round closed
  have hquart := hthm.2.2.1.mp (hthm.2.1.mp h52)
  refine ⟨toTits_frame c, fun i j hij a b => ?_, fun i j hij => ?_⟩
  · simp only [toTits, ← nativeCompactTitsEquiv_product, nativeCompactTitsEquiv_trace]
    exact c.overlap hij a b
  obtain ⟨B, hB, hi, hj⟩ := hquart i j hij
  refine ⟨B, hB.1, hi, hj, fun t ht hti htj => ?_⟩
  have hshare := planeShare_eq_one_iff_mem_quartet round closed hB hij hi hj hti htj
  rw [if_pos ht] at hshare
  have hle : nativeFramePlane (c.point t) ≤
      mixedProductSpace nativeEqualCubic (nativeFramePlane (c.point i))
        (nativeFramePlane (c.point j)) :=
    ((planeShare_sum_rule round closed).1 i j t hij hti htj).2.1.mp hshare
  -- the product space goes into `titsProdSpace`
  have hmix : mixedProductSpace nativeEqualCubic (nativeFramePlane (c.point i))
      (nativeFramePlane (c.point j)) ≤
      (titsProdSpace (titsFramePlane (toTits c i)) (titsFramePlane (toTits c j))).comap
        (nativeCompactTitsEquiv.toLinearEquiv.toLinearMap.comp
          (LinearMap.ker Glennie.traceLinear).subtype) := by
    rw [mixedProductSpace_eq_span, Submodule.map₂_le]
    intro x hx y hy
    change nativeCompactTitsEquiv ((nativeEqualCubic.L x y : NativeTraceless) : Glennie.Albert) ∈
      titsProdSpace (titsFramePlane (toTits c i)) (titsFramePlane (toTits c j))
    rw [nativeEqualCubic_L_coe', map_sub, map_smul, nativeCompactTitsEquiv_product,
      nativeCompactTitsEquiv_one]
    have hx' : nativeCompactTitsEquiv (x : Glennie.Albert) ∈ titsFramePlane (toTits c i) :=
      framePlane_to_tits (c.frame i) hx
    have hy' : nativeCompactTitsEquiv (y : Glennie.Albert) ∈ titsFramePlane (toTits c j) :=
      framePlane_to_tits (c.frame j) hy
    have hmem : CompactTits.product (nativeCompactTitsEquiv (x : Glennie.Albert))
        (nativeCompactTitsEquiv (y : Glennie.Albert)) ∈
        titsProdSpace (titsFramePlane (toTits c i)) (titsFramePlane (toTits c j)) :=
      Submodule.subset_span (Or.inr ⟨_, hx', _, hy', rfl⟩)
    have hone : CompactTits.one ∈
        titsProdSpace (titsFramePlane (toTits c i)) (titsFramePlane (toTits c j)) :=
      Submodule.subset_span (Or.inl rfl)
    exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ hone)
  rw [titsFramePlane, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hc := hmix (hle (center_mem_framePlane (c.frame t) a))
  rw [Submodule.mem_comap] at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, nativeCenter_coe] at hc
  rw [Glennie.traceless, show Glennie.trace (c.point t a) = 1 from (c.frame t).trace_one a,
    map_sub, map_smul,
    nativeCompactTitsEquiv_one] at hc
  exact hc

end

end ThirteenPlanes.AlbertGrading
