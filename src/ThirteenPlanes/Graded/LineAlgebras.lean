module

public import ThirteenPlanes.Graded.ReferenceGeometry
public import ThirteenPlanes.AllLinesGeometry

@[expose] public section

/-! The native fixed Jordan subalgebra of a projective line and its traceless qutrit model. -/

namespace ThirteenPlanes.Graded

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- The actual fixed subspace of the character with the specified line normal. -/
def lineAlgebra (l : SignedPlaneIndex) : Submodule ℝ Glennie.Albert :=
  LinearMap.ker ((nativeCharacterAction l.val.val).toLinearMap - LinearMap.id)

@[simp] theorem mem_lineAlgebra_iff (l : SignedPlaneIndex) (x : Glennie.Albert) :
    x ∈ lineAlgebra l ↔ nativeCharacterAction l.val.val x = x := by
  simp [lineAlgebra, LinearMap.mem_ker, sub_eq_zero]

theorem lineAlgebra_one (l : SignedPlaneIndex) : (1 : Glennie.Albert) ∈ lineAlgebra l :=
  (mem_lineAlgebra_iff l 1).mpr (nativeCharacterAction_one _)

theorem lineAlgebra_product (l : SignedPlaneIndex) {x y : Glennie.Albert}
    (hx : x ∈ lineAlgebra l) (hy : y ∈ lineAlgebra l) : Glennie.jordan x y ∈ lineAlgebra l := by
  rw [mem_lineAlgebra_iff] at hx hy ⊢
  rw [nativeCharacterAction_product, hx, hy]

theorem mem_lineAlgebra_iff_character_support (l : SignedPlaneIndex) (x : Glennie.Albert) :
    x ∈ lineAlgebra l ↔ ∀ q : Charge, chargeDot l.val.val q ≠ 0 →
      (nativeSignedCoordinates x).val q = 0 := by
  rw [mem_lineAlgebra_iff]
  let z := (nativeSignedCoordinates x).val
  constructor
  · intro hx q hq
    have he := congrFun ((nativeCharacterAction_coordinates l.val.val x).symm.trans
      (congrArg (fun a => (nativeSignedCoordinates a).val) hx)) q
    change chargePhase (chargeDot l.val.val q) * z q = z q at he
    by_contra hn
    apply hq
    exact FiniteGroup.chargePhase_injective (mul_right_cancel₀ hn (he.trans (one_mul _).symm))
  · intro hx
    apply nativeSignedCoordinates.injective
    apply Subtype.ext
    rw [nativeCharacterAction_coordinates]
    funext q
    by_cases hq : chargeDot l.val.val q = 0
    · rw [characterAction_apply, hq, chargePhase_zero, one_mul]
    · rw [characterAction_apply, hx q hq, mul_zero]

/-- The traceless part of the line subalgebra. -/
def lineTraceless (l : SignedPlaneIndex) : Submodule ℝ NativeTraceless :=
  (lineAlgebra l).comap Glennie.traceLinear.ker.subtype

theorem lineTraceless_closed (l : SignedPlaneIndex) :
    IsClosedPiece nativeEqualCubic (lineTraceless l) := by
  intro x y hx hy
  change Glennie.traceless (Glennie.jordan x y) ∈ lineAlgebra l
  change (x : Glennie.Albert) ∈ lineAlgebra l at hx
  change (y : Glennie.Albert) ∈ lineAlgebra l at hy
  exact (lineAlgebra l).sub_mem (lineAlgebra_product l hx hy)
    ((lineAlgebra l).smul_mem _ (lineAlgebra_one l))

/-- The concrete octet on a projective line is the traceless Hermitian three-by-three
complex Jordan model, with the actual trace product and each of the four planes identified. -/
theorem nativeLineTracelessModel (l : SignedPlaneIndex) :
    ∃ (j : TracelessHermitian3 →ₗᵢ[ℝ] NativeTraceless) (e : Fin 4 ≃ ChargeLinePoint l.val),
      LinearMap.range j.toLinearMap = lineTraceless l ∧
      (∀ k, (matrixPlane k).map j.toLinearMap = plane (e k).val) ∧
      (∀ x y, j (TracelessHermitian3.jordan x y) = nativeCenteredJordan (j x) (j y)) := by
  obtain ⟨j₀, e, hj₀, hp, hc₀⟩ := matrixLine_over_any_normal_geometry l.val
  let j := signedNativeEquiv.toLinearIsometry.comp j₀
  have hj (x : TracelessHermitian3) : j x = signedNativeEquiv (j₀ x) := rfl
  have hrange : LinearMap.range j.toLinearMap = lineTraceless l := by
    ext x
    obtain ⟨y, rfl⟩ := signedNativeEquiv.surjective x
    have hmem : signedNativeEquiv y ∈ LinearMap.range j.toLinearMap ↔
        y ∈ LinearMap.range j₀.toLinearMap := by
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, signedNativeEquiv.injective ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
    rw [hmem, hj₀]
    change _ ↔ (signedNativeEquiv y : Glennie.Albert) ∈ lineAlgebra l
    rw [mem_lineAlgebra_iff_character_support, nativeSignedCoordinates_signedNative]
    constructor
    · intro h q hq
      have hn : q ≠ 0 := by
        rintro rfl
        exact hq (by simp [chargeDot])
      exact (signedExtend_nonzero y ⟨q, hn⟩).trans (h ⟨q, hn⟩ hq)
    · intro h q hq
      rw [← signedExtend_nonzero]
      exact h q.val hq
  have hC (x y z : TracelessHermitian3) :
      nativeEqualCubic.apply (j x) (j y) (j z) = matrixEqualCubic.apply x y z := by
    rw [hj, hj, hj, ← signedEqualCubic_eq_native]
    have hh := hc₀ (1, 1) x y z
    change (interactionCubic signedPair 1).apply (j₀ x) (j₀ y) (j₀ z) =
      (interactionCubic fourPlanePair 1).apply x y z at hh
    simpa only [interactionCubic_fourPlanePair_one, signedPair_at_one] using hh
  refine ⟨j, e, hrange, ?_, ?_⟩
  · intro k
    change (matrixPlane k).map (signedNativeEquiv.toLinearMap.comp j₀.toLinearMap) = _
    rw [Submodule.map_comp, hp, plane]
  · intro x y
    have hx (u : TracelessHermitian3) : j u ∈ lineTraceless l :=
      hrange ▸ ⟨u, rfl⟩
    have hy := lineTraceless_closed l (hx x) (hx y)
    rw [← hrange] at hy
    obtain ⟨z, hz⟩ := hy
    change j z = nativeCenteredJordan (j x) (j y) at hz
    rw [← hz]
    congr 1
    apply ext_inner_right ℝ
    intro w
    calc
      ⟪TracelessHermitian3.jordan x y, w⟫ =
          ⟪nativeCenteredJordan (j x) (j y), j w⟫ := (hC x y w).symm
      _ = ⟪j z, j w⟫ := by rw [hz]
      _ = ⟪z, w⟫ := LinearIsometry.inner_map_map (𝕜 := ℝ) j z w

theorem lineTraceless_eq_plane_sum (l : SignedPlaneIndex) :
    lineTraceless l = ⨆ p : ChargeLinePoint l.val, plane p.val := by
  obtain ⟨j, e, hrange, hp, _⟩ := nativeLineTracelessModel l
  rw [← hrange, ← e.surjective.iSup_comp]
  simp_rw [← hp]
  rw [← Submodule.map_iSup]
  change LinearMap.range j.toLinearMap =
    (⨆ k, fourPlaneDecomposition.plane k).map j.toLinearMap
  rw [fourPlaneDecomposition.exhaustive, Submodule.map_top]

/-- Every outcome of each of the four joined native frames belongs to the line algebra. -/
theorem point_mem_lineAlgebra {p l : SignedPlaneIndex}
    (hp : signedPointOnLine p l) (a : Fin 3) : point p a ∈ lineAlgebra l := by
  have hplane : plane p ≤ lineTraceless l := by
    rw [lineTraceless_eq_plane_sum]
    exact le_iSup (fun t : ChargeLinePoint l.val => plane t.val) ⟨p, hp⟩
  have hc : nativeCenter (point p a) ∈ lineTraceless l := by
    apply hplane
    rw [center_point, plane_eq_range]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  change (nativeCenter (point p a) : Glennie.Albert) ∈ lineAlgebra l at hc
  have he : (nativeCenter (point p a) : Glennie.Albert) + (1 / 3 : ℝ) • 1 = point p a := by
    rw [nativeCenter_coe, Glennie.traceless, (isFrame p).trace_one, sub_add_cancel]
  rw [← he]
  exact (lineAlgebra l).add_mem hc ((lineAlgebra l).smul_mem _ (lineAlgebra_one l))

end

end ThirteenPlanes.Graded
