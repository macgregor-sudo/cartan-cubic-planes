module

public import ThirteenPlanes.Cartan.GradedRecutAction
public import ThirteenPlanes.Cartan.AlbertDerivationComplexTrace
public import ThirteenPlanes.JordanFrames.Albert

@[expose] public section

/-! Transport the native F₄ torus and its frame by the same Albert automorphism. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.Cartan

noncomputable section

/-- The actual map from full native Albert derivations to traceless skew operators. -/
abbrev nativeAlbertRestrictDerivation : NativeAlbertDerivations →ₗ[ℝ] SkewOperator albertJordan.traceFree :=
  albertJordan.restrictDerivation.comp nativeAlbertDerivationSkewEquiv.toLinearMap

/-- The trace representation of a native Lie subalgebra. -/
abbrev nativeAlbertRestrictedCartan (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    Submodule ℝ (SkewOperator albertJordan.traceFree) :=
  T.toSubmodule.map nativeAlbertRestrictDerivation

theorem nativeAlbertRestrictedCartan_eq_traceMap (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    nativeAlbertRestrictedCartan T =
      (T.toSubmodule.map nativeAlbertDerivationTraceEquiv.toLinearMap).map
        albertDerivationOperators.subtype := by
  rw [← Submodule.map_comp]
  rfl

theorem nativeAlbertRestrictDerivation_map (g : Glennie.CompactAutomorphism)
    (D : NativeAlbertDerivations) :
    nativeAlbertRestrictDerivation (nativeAlbertLieAction g D) =
      conjugateSkew ((albertJordanAction g).traceAction albertJordan)
        (nativeAlbertRestrictDerivation D) := by
  change albertJordan.restrictDerivation (nativeAlbertDerivationSkewEquiv (nativeAlbertLieAction g D)) =
    conjugateSkew ((albertJordanAction g).traceAction albertJordan)
      (albertJordan.restrictDerivation (nativeAlbertDerivationSkewEquiv D))
  rw [(albertJordanAction g).conjugate_restrictDerivation albertJordan]
  apply congrArg albertJordan.restrictDerivation
  apply Subtype.ext
  apply Subtype.ext
  exact nativeAlbertLieAction_val g D

theorem nativeAlbertRestrictedCartan_map (g : Glennie.CompactAutomorphism)
    (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    nativeAlbertRestrictedCartan (T.map (nativeAlbertLieAction g).toLieHom) =
      (nativeAlbertRestrictedCartan T).map
        (conjugateSkew ((albertJordanAction g).traceAction albertJordan)).toLinearMap := by
  change (T.toSubmodule.map (nativeAlbertLieAction g).toLinearEquiv.toLinearMap).map
    nativeAlbertRestrictDerivation = _
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

/-- The restricted common kernel is the literal native fixed space. -/
theorem nativeAlbertRestrictedCartan_fixed_eq (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    (fixedSpace (nativeAlbertRestrictedCartan T)).map albertTraceEquiv.toLinearMap = albertRealFixed T := by
  ext x
  rw [mem_albertRealFixed]
  constructor
  · rintro ⟨y, hy, rfl⟩ D hD
    have hz := (mem_fixedSpace _ y).mp hy
      ⟨nativeAlbertRestrictDerivation D, Submodule.mem_map_of_mem hD⟩
    exact congrArg Subtype.val hz
  · intro hx
    let y := albertTraceEquiv.symm x
    have hy : albertTraceEquiv y = x := albertTraceEquiv.apply_symm_apply x
    refine ⟨y, (mem_fixedSpace _ y).mpr ?_, hy⟩
    rintro ⟨_, D, hD, rfl⟩
    apply Subtype.ext
    change D.val y.val = 0
    rw [← show y.val = x.val from congrArg Subtype.val hy] at hx
    exact hx D hD

theorem nativeAlbertRestrictedCartan_fixed_map (g : Glennie.CompactAutomorphism)
    (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    fixedSpace (nativeAlbertRestrictedCartan (T.map (nativeAlbertLieAction g).toLieHom)) =
      (fixedSpace (nativeAlbertRestrictedCartan T)).map
        ((albertJordanAction g).traceAction albertJordan).toLinearMap := by
  rw [nativeAlbertRestrictedCartan_map, fixedSpace_conjugate]

theorem nativeAlbertRestrictedCartan_projection_map (g : Glennie.CompactAutomorphism)
    (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    projection (fixedSpace (nativeAlbertRestrictedCartan (T.map (nativeAlbertLieAction g).toLieHom))) =
      ((albertJordanAction g).traceAction albertJordan).toLinearEquiv.conj
        (projection (fixedSpace (nativeAlbertRestrictedCartan T))) := by
  rw [nativeAlbertRestrictedCartan_fixed_map, projection_map_isometry]

theorem nativeAlbertRestrictedCartan_casimir_map (g : Glennie.CompactAutomorphism)
    (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    operatorCasimir (nativeAlbertRestrictedCartan (T.map (nativeAlbertLieAction g).toLieHom)) =
      ((albertJordanAction g).traceAction albertJordan).toLinearEquiv.conj
        (operatorCasimir (nativeAlbertRestrictedCartan T)) := by
  rw [nativeAlbertRestrictedCartan_map, operatorCasimir_conjugate]

/-- The trace metric on the actual traceless derivation representation is preserved. -/
theorem nativeAlbertRestricted_metric_map (g : Glennie.CompactAutomorphism)
    (D E : NativeAlbertDerivations) :
    ⟪nativeAlbertRestrictDerivation (nativeAlbertLieAction g D),
      nativeAlbertRestrictDerivation (nativeAlbertLieAction g E)⟫ =
      ⟪nativeAlbertRestrictDerivation D, nativeAlbertRestrictDerivation E⟫ := by
  rw [nativeAlbertRestrictDerivation_map, nativeAlbertRestrictDerivation_map,
    LinearIsometryEquiv.inner_map_map]

/-- All four frame-type data are transported by the actual ambient Jordan automorphism. -/
theorem nativeAlbertCartan_frameType_map (g : Glennie.CompactAutomorphism)
    (T : LieSubalgebra ℝ NativeAlbertDerivations) {rank : ℕ} {κ : ℝ}
    (h : IsFrameType (nativeAlbertRestrictedCartan T) rank κ) :
    IsFrameType (nativeAlbertRestrictedCartan (T.map (nativeAlbertLieAction g).toLieHom)) rank κ := by
  rw [nativeAlbertRestrictedCartan_map]
  exact (conjugate_frameType_fixed ((albertJordanAction g).traceAction albertJordan) _ h).1

/-- The plane of the transported frame is the transported plane. -/
theorem nativeAlbertFramePlane_map (g : Glennie.CompactAutomorphism)
    {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    nativeFramePlane (fun i => g.equiv (p i)) =
      (nativeFramePlane p).map (albertTracelessAction g).toLinearMap := by
  rw [JordanFrames.native_framePlane_eq_centered_span (g.map_frame p hp),
    JordanFrames.native_framePlane_eq_centered_span hp, Submodule.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  apply Subtype.ext
  exact (g.map_traceless (p i)).symm

/-- A frame and the equality identifying its plane as a fixed space transport together. -/
theorem nativeAlbertFixed_frame_transport (g : Glennie.CompactAutomorphism)
    (T : LieSubalgebra ℝ NativeAlbertDerivations) {p : Fin 3 → Glennie.Albert}
    (hp : Glennie.Frame p) (h : albertRealFixed T = nativeFramePlane p) :
    Glennie.Frame (fun i => g.equiv (p i)) ∧
      albertRealFixed (T.map (nativeAlbertLieAction g).toLieHom) =
        nativeFramePlane (fun i => g.equiv (p i)) := by
  refine ⟨g.map_frame p hp, ?_⟩
  rw [albertRealFixed_map, h, nativeAlbertFramePlane_map g hp]

end

end ThirteenPlanes.Cartan
