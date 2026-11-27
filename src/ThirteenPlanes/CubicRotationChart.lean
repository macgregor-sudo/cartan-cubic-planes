module

public import ThirteenPlanes.CubicRotation
public import ThirteenPlanes.SignedFloorHessian

@[expose] public section

set_option backward.privateInPublic true

/-! Local coordinates around the orthogonal orbit of the actual signed floor cubic. -/

open scoped ContDiff RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

open SymmetricCubic

/-- The orthogonal normal space of the infinitesimal rotations. -/
abbrev rotationNormal (C : SymmetricCubic V) := (rotationSpace C)ᗮ

private def skewTangent (C : SymmetricCubic V) : skewEnd V →ₗ[ℝ] rotationSpace C :=
  ((insertLin C).comp (skewEnd V).subtype).codRestrict (rotationSpace C)
    (fun A => mem_rotationSpace.mpr ⟨A,A.property,rfl⟩)

private theorem skewTangent_surjective (C : SymmetricCubic V) : Function.Surjective (skewTangent C) := by
  intro D
  obtain ⟨A,hA,hD⟩ := mem_rotationSpace.mp D.property
  exact ⟨⟨A,hA⟩,Subtype.ext hD⟩

private theorem skewTangent_has_section (C : SymmetricCubic V) :
    ∃ S : rotationSpace C →ₗ[ℝ] skewEnd V, (skewTangent C).comp S = LinearMap.id :=
  (skewTangent C).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (skewTangent_surjective C))

private def skewSection (C : SymmetricCubic V) : rotationSpace C →ₗ[ℝ] skewEnd V :=
  (skewTangent_has_section C).choose

private theorem insert_skewSection (C : SymmetricCubic V) (p : rotationSpace C) :
    C.insert ((skewSection C p : skewEnd V) : V →ₗ[ℝ] V) = p := by
  have h := congrArg (fun M : rotationSpace C →ₗ[ℝ] rotationSpace C => (M p : SymmetricCubic V))
    (skewTangent_has_section C).choose_spec
  exact h

private def skewGenerator (C : SymmetricCubic V) : rotationSpace C →L[ℝ] V →L[ℝ] V :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    ((skewEnd V).subtype.comp (skewSection C))).toContinuousLinearMap

/-- Coordinates given by exponentiation along the orbit and translation in its normal space. -/
def rotationChart (C : SymmetricCubic V) (p : rotationSpace C × rotationNormal C) : SymmetricCubic V :=
  C.exponentialPullback (skewGenerator C p.1) + (p.2 : SymmetricCubic V)

@[simp] theorem rotationChart_zero (C : SymmetricCubic V) : rotationChart C 0 = C := by
  simp [rotationChart]

/-- The zero-normal slice is an actual orthogonal orbit of the cubic. -/
theorem rotationChart_slice (C : SymmetricCubic V) (p : rotationSpace C) :
    ∃ U : V ≃ₗᵢ[ℝ] V, rotationChart C (p,0) = C.pullback U.toLinearMap := by
  let A := skewSection C p
  have hA : IsSkew (A : V →ₗ[ℝ] V) := mem_skewEnd.mp A.property
  let S := skewRotation (A : V →ₗ[ℝ] V) hA
  refine ⟨S,?_⟩
  apply SymmetricCubic.ext
  intro x y z
  have hu (u : V) : S.toLinearMap u = NormedSpace.exp (skewGenerator C p) u :=
    skewRotation_apply (A : V →ₗ[ℝ] V) hA u
  simp only [rotationChart,Submodule.coe_zero,add_zero,exponentialPullback,
    pullback_apply,ContinuousLinearMap.coe_coe,hu]

/-- The derivative of the rotation chart is its orthogonal direct sum equivalence. -/
def rotationChartLinearEquiv (C : SymmetricCubic V) :
    (rotationSpace C × rotationNormal C) ≃L[ℝ] SymmetricCubic V :=
  ((rotationSpace C).prodEquivOfIsCompl _ (rotationSpace C).isCompl_orthogonal).toContinuousLinearEquiv

theorem rotationChartLinearEquiv_apply (C : SymmetricCubic V) (p : rotationSpace C × rotationNormal C) :
    rotationChartLinearEquiv C p = (p.1 : SymmetricCubic V) + (p.2 : SymmetricCubic V) := rfl

theorem rotationChart_contDiff (C : SymmetricCubic V) (n : ℕ∞ω) : ContDiff ℝ n (rotationChart C) := by
  have h₁ : ContDiff ℝ n (fun p : rotationSpace C × rotationNormal C =>
      C.exponentialPullback (skewGenerator C p.1)) :=
    (C.exponentialPullback_contDiff n).comp ((skewGenerator C).contDiff.comp contDiff_fst)
  have h₂ : ContDiff ℝ n (fun p : rotationSpace C × rotationNormal C => (p.2 : SymmetricCubic V)) :=
    (rotationNormal C).subtypeL.contDiff.comp contDiff_snd
  exact h₁.add h₂

theorem rotationChart_hasFDerivAt (C : SymmetricCubic V) :
    HasFDerivAt (rotationChart C) (rotationChartLinearEquiv C).toContinuousLinearMap 0 := by
  let L := (skewGenerator C).comp (ContinuousLinearMap.fst ℝ (rotationSpace C) (rotationNormal C))
  let R := (rotationNormal C).subtypeL.comp (ContinuousLinearMap.snd ℝ (rotationSpace C) (rotationNormal C))
  have hD := C.exponentialPullback_hasFDerivAt
  have hD' : HasFDerivAt C.exponentialPullback
      (((insertLin C).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap) (L 0) := by
    rwa [map_zero]
  have h := (hD'.comp (0 : rotationSpace C × rotationNormal C) L.hasFDerivAt).add (R.hasFDerivAt (x := 0))
  change HasFDerivAt (rotationChart C) _ _ at h
  convert h using 1
  apply ContinuousLinearMap.ext
  intro p
  change (p.1 : SymmetricCubic V) + (p.2 : SymmetricCubic V) =
    C.insert ((skewSection C p.1 : skewEnd V) : V →ₗ[ℝ] V) + (p.2 : SymmetricCubic V)
  rw [insert_skewSection]

/-- At the actual signed floor, the A-Hessian bounds the full square norm orthogonal to rotations. -/
theorem signedFloorCubic_normal_hessian (y : rotationNormal signedFloorCubic) :
    ‖y‖^2 ≤ aHessian signedFloorCubic y y := by
  let C := signedFloorCubic
  have hn : 0 < Module.finrank ℝ SignedField := by rw [signedField_finrank]; decide
  have hfloor := signedFloorCubic_aFunction
  obtain ⟨⟨r,t,w⟩,hsum,_⟩ := existsUnique_decomposition hn hfloor (y : SymmetricCubic SignedField)
  change (r : SymmetricCubic SignedField) + t + w = y at hsum
  have hry : ⟪(r : SymmetricCubic SignedField),(y : SymmetricCubic SignedField)⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal r.property y.property
  have hrt := rotation_orth_trace hn hfloor r.property t.property
  have hrw := rotation_orth_complement r.property w.property
  rw [← hsum,inner_add_right,inner_add_right,inner_eq_tensorPairing,inner_eq_tensorPairing,
    inner_eq_tensorPairing,hrt,hrw,add_zero,add_zero] at hry
  have hr0 : (r : SymmetricCubic SignedField) = 0 := eq_zero_of_tensorPairing_self _ hry
  have hy : (t : SymmetricCubic SignedField) + (w : SymmetricCubic SignedField) = y := by
    simpa only [hr0,zero_add] using hsum
  have htw := trace_orth_complement t.property w.property
  have hnorm : ‖y‖^2 = t.val.tensorPairing t.val + w.val.tensorPairing w.val := by
    calc
      ‖y‖^2 = ⟪(y : SymmetricCubic SignedField),(y : SymmetricCubic SignedField)⟫ :=
        (real_inner_self_eq_norm_sq y).symm
      _ = _ := by rw [← hy,inner_add_right,inner_add_left,inner_add_left,inner_eq_tensorPairing,
                    inner_eq_tensorPairing,inner_eq_tensorPairing,inner_eq_tensorPairing,
                    htw,tensorPairing_comm w.val t.val,htw,zero_add,add_zero]
  have hh := aHessian_spectral_self hn hfloor r.property t.property w.property
  rw [hsum,signedField_finrank,traceEigenvalue_twentySix] at hh
  rw [hnorm,hh]
  linarith only [tensorPairing_self_nonneg t.val]

end
end ThirteenPlanes
