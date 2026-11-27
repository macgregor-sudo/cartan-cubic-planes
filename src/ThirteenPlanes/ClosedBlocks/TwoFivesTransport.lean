module

public import ThirteenPlanes.ClosedBlocks.HarmonicPatterns
public import ThirteenPlanes.ClosedBlocks.TwoFivesNormalized
public import ThirteenPlanes.Cartan.AlbertInvariant
public import SubalgebraCoordsAndLine

@[expose] public section

set_option backward.privateInPublic true

/-! Transport the standard real-complement calculation using an actual Albert automorphism. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce AlbertSequential AlbertSequential.NativeAnalysis

noncomputable section

private def standardRealTraceless : Submodule ℝ NativeTraceless :=
  (H3Subalgebra .R).carrier.comap nativeCoordinates

private theorem native_action_preserves_cubic (g : Glennie.CompactAutomorphism) :
    nativeEqualCubic =
      nativeEqualCubic.pullback (Cartan.albertTracelessAction g).toLinearMap := by
  apply SymmetricCubic.ext
  intro x y z
  rw [SymmetricCubic.pullback_apply]
  change Glennie.inner (Glennie.traceless (Glennie.jordan x.val y.val)) z.val =
    Glennie.inner (Glennie.traceless (Glennie.jordan (g.equiv x.val) (g.equiv y.val))) (g.equiv z.val)
  rw [← g.map_jordan, ← g.map_traceless, g.inner_map]

private theorem native_action_raw (g : NativeAlbertAutomorphism) (x : NativeTraceless) :
    nativeCoordinates (Cartan.albertTracelessAction (nativeAutoToCompactAuto g) x) =
      g.linearEquiv (nativeCoordinates x) := by
  change recoveredCoordinateEquiv.symm ((nativeAutoToCompactAuto g).equiv x.val) = _
  rw [nativeAutoToCompactAuto_apply, LinearEquiv.symm_apply_apply]
  rfl

private theorem centered_in_real_standard {y : Albert} (hy : y ∈ (H3Subalgebra .R).carrier) :
    nativeCenter (recoveredCoordinateEquiv y) ∈ standardRealTraceless := by
  change recoveredCoordinateEquiv.symm (Glennie.traceless (recoveredCoordinateEquiv y)) ∈
    (H3Subalgebra .R).carrier
  rw [Glennie.traceless, map_sub, map_smul, ← recoveredCoordinateEquiv_unit,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact (H3Subalgebra .R).carrier.sub_mem hy
    ((H3Subalgebra .R).carrier.smul_mem _ (H3Subalgebra .R).unit_mem)

private theorem trace_pairing_of_realOrthogonal {S : Submodule ℝ NativeTraceless}
    (ho : standardRealTraceless.IsOrtho S) (x : S) (y : Albert)
    (hy : y ∈ (H3Subalgebra .R).carrier) :
    AlbertSequential.tracePairing (nativeCoordinates x.val) y = 0 := by
  rw [← recoveredCoordinateEquiv_tracePairing]
  change Glennie.inner (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm x.val.val))
    (recoveredCoordinateEquiv y) = 0
  rw [LinearEquiv.apply_symm_apply, Glennie.inner_comm]
  have h := ho.inner_eq (centered_in_real_standard hy) x.property
  change Glennie.inner (Glennie.traceless (recoveredCoordinateEquiv y)) x.val.val = 0 at h
  rw [nativeInner_center_left] at h
  exact h

private theorem diagonal_zero_of_ortho_real {S : Submodule ℝ NativeTraceless}
    (ho : standardRealTraceless.IsOrtho S) (x : S) (i : Fin 3) :
    (nativeCoordinates x.val).1 i = 0 := by
  have h := trace_pairing_of_realOrthogonal ho x (diagAtom i) (diagAtom_mem_H3Subalgebra .R i)
  simpa only [tracePairing_comm (nativeCoordinates x.val), tracePairing_diagAtom] using h

private theorem real_upperSlot_mem (i : Fin 3) : upperSlot i octOne ∈ (H3Subalgebra .R).carrier := by
  rw [H3Subalgebra, mem_jordanSubalgebraH3_iff]
  fin_cases i <;> exact ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

private theorem real_zero_of_ortho_real {S : Submodule ℝ NativeTraceless}
    (ho : standardRealTraceless.IsOrtho S) (x : S) (i : Fin 3) :
    ((nativeCoordinates x.val).2 i).1.re = 0 := by
  have hh := trace_pairing_of_realOrthogonal ho x _ (real_upperSlot_mem i)
  have hr (p : AlbertSequential.Octonion) : octDot p octOne = p.1.re := by
    rw [octDot_eq_coords]
    change p.1.re * 1 + p.1.imI * 0 + p.1.imJ * 0 + p.1.imK * 0 +
      p.2.re * 0 + p.2.imI * 0 + p.2.imJ * 0 + p.2.imK * 0 = _
    ring
  rw [tracePairing_eq_coords] at hh
  fin_cases i <;> simp [upperSlot, octDot_zero_right, hr] at hh <;> exact hh

/-- Normalization of the actual embedded real Cartan subalgebra. -/
def NativeRealBlockNormalization : Prop :=
  ∀ U : Submodule ℝ NativeTraceless, IsClosedPiece nativeEqualCubic U →
    ∀ I : U ≃ₗᵢ[ℝ] RealTracelessSymmetric3,
      nativeEqualCubic.pullback (W := ↥U) U.subtype =
        (Real.sqrt 6)⁻¹ • realCartanCubic.pullback (W := ↥U) I.toLinearMap →
      ∃ g : NativeAlbertAutomorphism, ∀ x : NativeTraceless,
        g.linearEquiv (recoveredCoordinateEquiv.symm x.val) ∈ (H3Subalgebra .R).carrier ↔ x ∈ U

/-- Assemble the native exclusion of two orthogonal real Cartan blocks from
the real block normal form and the Gram multiplicity bound for real derivations. -/
theorem nativeNoTwoFives_of_normalization_and_derivation_bound
    (normalize : NativeRealBlockNormalization)
    (derivation_bound : ∀ D : Module.End ℝ RealTracelessSymmetric3,
      (∀ x y, D (realCartanCubic.L x y) = realCartanCubic.L (D x) y + realCartanCubic.L x (D y)) →
      (∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫) →
      ∀ t : ℝ, 0 < t → Module.finrank ℝ (LinearMap.ker ((LinearMap.adjoint (𝕜 := ℝ) (E := ↥RealTracelessSymmetric3)
          (F := ↥RealTracelessSymmetric3) D).comp D - t • LinearMap.id)) ≤ 2) :
    NativeNoTwoFives := by
  intro U S clu cls ho tfu tfs du ds
  obtain ⟨I, hI⟩ := harmonic_round_five_cartan
    (closedSubspace_restriction_isRound Graded.nativeRound clu) tfu du
  have hscale : Real.sqrt (1 / 6) = (Real.sqrt 6)⁻¹ := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, one_div]
  rw [hscale] at hI
  obtain ⟨g, hg⟩ := normalize U clu I hI
  let G := nativeAutoToCompactAuto g
  let J := Cartan.albertTracelessAction G
  let T := S.map J.toLinearMap
  have hU : U.map J.toLinearMap = standardRealTraceless := by
    ext y
    obtain ⟨x, rfl⟩ := J.surjective y
    change J x ∈ Submodule.map J.toLinearMap U ↔ nativeCoordinates (J x) ∈ (H3Subalgebra .R).carrier
    rw [native_action_raw]
    change _ ↔ g.linearEquiv (recoveredCoordinateEquiv.symm x.val) ∈ (H3Subalgebra .R).carrier
    rw [hg]
    constructor
    · rintro ⟨a, ha, he⟩
      have hx : a = x := J.injective he
      exact hx ▸ ha
    · exact fun hx => ⟨x, hx, rfl⟩
  have hoT : standardRealTraceless.IsOrtho T := by
    rw [← hU]
    exact isOrtho_map_isometry J ho
  have hJ := native_action_preserves_cubic G
  have hcT : IsClosedPiece nativeEqualCubic T := isClosedPiece_map_isometry J hJ cls
  have htT : (nativeEqualCubic.pullback (W := ↥T) T.subtype).TraceFree := by
    have hh := @traceFree_pullback_iff ↥S ↥T
      inferInstance (Submodule.innerProductSpace S) inferInstance
      inferInstance (Submodule.innerProductSpace T)
      (nativeEqualCubic.pullback (W := ↥T) T.subtype) (mapBlockIsometry J S)
    apply hh.mp
    rw [← pullback_block_map, ← hJ]
    exact tfs
  have hdT : Module.finrank ℝ T = 5 :=
    (mapBlockIsometry J S).toLinearEquiv.finrank_eq.symm.trans ds
  exact noFiveInStandardRealComplement_of_derivation_bound hcT
    (diagonal_zero_of_ortho_real hoT) (real_zero_of_ortho_real hoT) htT hdT derivation_bound

end

end ThirteenPlanes.ClosedBlocks
