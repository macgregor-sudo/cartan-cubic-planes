module

public import ThirteenPlanes.Basic
public import ThirteenPlanes.FourPlanesPlaneData
public import ThirteenPlanes.PilotContractions

@[expose] public section

/-! A concrete model of the geometric hypotheses in Section 9.

The field space is the eight-dimensional real space of traceless Hermitian three-by-three complex
matrices with the trace metric. The cubic is given by the trace-free Jordan product. The four
planes consist of traceless matrices diagonal in the four mutually unbiased qutrit bases.
The model satisfies `IsRound`, `IsClosedPlaneSystem` and `SymmetricCubic.TraceFree`. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.PencilFlow.Proofs

open ThirteenPlanes ThirteenPlanes.PlaneContractions

noncomputable section

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι]

/-- A cubic whose plane restrictions are trace-free and which satisfies the repeated-plane rule is
trace-free. -/
theorem traceFree_of_planes (planes : PlaneDecomposition V ι) (d : SymmetricCubic V)
    (hrep : ∀ i (x y : planes.plane i) (z : (planes.plane i)ᗮ), d.apply x y z = 0)
    (htf : ∀ i, (planes.restriction i d).TraceFree) : d.TraceFree := by
  intro z
  have hid : d.L z = ∑ i, d.L z ∘ₗ ((planes.plane i).subtype ∘ₗ piP planes i) := by
    ext v
    rw [LinearMap.sum_apply]
    conv_lhs => rw [← sum_proj_apply planes v]
    rw [map_sum]
    rfl
  rw [hid, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hc := compress_slice hrep i z
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  refine (congrArg (LinearMap.trace ℝ (planes.plane i)) hc).trans ?_
  exact htf i _

end General

/-- The field space of the four-plane model: traceless Hermitian `3 × 3` complex matrices. -/
abbrev FourPlaneSpace : Type := TracelessHermitian3

/-- The round cubic of the four-plane model: the trace-free Jordan product. -/
abbrev fourPlaneCubic : SymmetricCubic FourPlaneSpace := matrixEqualCubic

/-- The four trace-free diagonal planes. -/
abbrev fourPlanes : PlaneDecomposition FourPlaneSpace (Fin 4) := fourPlaneDecomposition

theorem fourPlaneCubic_isRound : IsRound fourPlaneCubic (1 / 6) where
  positive := by norm_num
  square_norm := by
    intro x
    have h := fourPlane_squareLaw x
    rw [interactionCubic_fourPlanePair_one] at h
    rw [h]
    ring

theorem fourPlaneCubic_isClosedPlaneSystem : IsClosedPlaneSystem fourPlaneCubic fourPlanes := by
  intro k x y hx hy
  change TracelessHermitian3.jordan x y ∈ matrixPlane k
  exact (mem_matrixPlane_iff k _).2 (project_jordan_of_fixed k _ _
    ((mem_matrixPlane_iff k _).1 hx) ((mem_matrixPlane_iff k _).1 hy))

theorem fourPlaneCubic_traceFree : fourPlaneCubic.TraceFree := by
  have h := traceFree_of_planes fourPlanes (interactionCubic fourPlanePair 1)
    fourPlaneData.repeatedPlane fourPlaneData.traceFree
  rwa [interactionCubic_fourPlanePair_one] at h

theorem fourPlaneSpace_finrank : Module.finrank ℝ FourPlaneSpace = 8 := fourPlane_dimension

instance fourPlaneSpace_nontrivial : Nontrivial FourPlaneSpace :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [fourPlaneSpace_finrank]; norm_num)

/-- Non-vacuity of the Section 9 geometric inputs: a Euclidean field space with an exhaustive
orthogonal system of at least two closed two-planes for a round cubic. -/
theorem exists_closedPlaneModel :
    ∃ (m : ℕ) (_ : 2 ≤ m) (h : SymmetricCubic FourPlaneSpace) (c : ℝ)
      (planes : PlaneDecomposition FourPlaneSpace (Fin m)),
      IsRound h c ∧ IsClosedPlaneSystem h planes :=
  ⟨4, by norm_num, fourPlaneCubic, 1 / 6, fourPlanes, fourPlaneCubic_isRound,
    fourPlaneCubic_isClosedPlaneSystem⟩

/-- The same model also satisfies the `HessianA/B/C` inputs: the field space is nontrivial and the
cubic is trace-free and round. -/
theorem exists_closedPlaneModel_traceFree :
    ∃ (m : ℕ) (_ : 2 ≤ m) (h : SymmetricCubic FourPlaneSpace) (c : ℝ)
      (planes : PlaneDecomposition FourPlaneSpace (Fin m)),
      Nontrivial FourPlaneSpace ∧ h.TraceFree ∧ IsRound h c ∧ IsClosedPlaneSystem h planes :=
  ⟨4, by norm_num, fourPlaneCubic, 1 / 6, fourPlanes, inferInstance, fourPlaneCubic_traceFree,
    fourPlaneCubic_isRound, fourPlaneCubic_isClosedPlaneSystem⟩

/-- Universe-polymorphic form over `Type`: there is a Euclidean type carrying the model. -/
theorem exists_closedPlaneModel_type :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V)
      (_ : FiniteDimensional ℝ V) (m : ℕ) (_ : 2 ≤ m) (h : SymmetricCubic V) (c : ℝ)
      (planes : PlaneDecomposition V (Fin m)),
      Nontrivial V ∧ h.TraceFree ∧ IsRound h c ∧ IsClosedPlaneSystem h planes :=
  ⟨FourPlaneSpace, inferInstance, inferInstance, inferInstance, 4, by norm_num, fourPlaneCubic,
    1 / 6, fourPlanes, inferInstance, fourPlaneCubic_traceFree, fourPlaneCubic_isRound,
    fourPlaneCubic_isClosedPlaneSystem⟩

end

end ThirteenPlanes.PencilFlow.Proofs
