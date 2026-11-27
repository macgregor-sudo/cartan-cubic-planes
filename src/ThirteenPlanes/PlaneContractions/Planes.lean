module

public import ThirteenPlanes.PlaneContractions.General

@[expose] public section

/-! Geometry of an exhaustive orthogonal plane decomposition: projections, compressed slices and
the trace identities for the diagonal cubic. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace PlaneContractions

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} (planes : PlaneDecomposition V ι)

/-- Orthogonal projection onto a plane, valued in the plane. -/
def piP (i : ι) : V →ₗ[ℝ] planes.plane i :=
  (planes.plane i).orthogonalProjectionOnto.toLinearMap

theorem proj_eq (i : ι) : planes.proj i = (planes.plane i).subtype ∘ₗ piP planes i := rfl

theorem piP_subtype (i : ι) : piP planes i ∘ₗ (planes.plane i).subtype = LinearMap.id := by
  ext u
  simp [piP, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem piP_subtype_ne {i j : ι} (hij : i ≠ j) :
    piP planes i ∘ₗ (planes.plane j).subtype = 0 := by
  ext u
  simp only [piP, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    ContinuousLinearMap.coe_coe, LinearMap.zero_apply, ZeroMemClass.coe_zero,
    ZeroMemClass.coe_eq_zero]
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  exact (planes.pairwise_orthogonal hij.symm).le u.2

theorem sub_mem_orthogonal (i : ι) (z : V) :
    z - ((piP planes i z : planes.plane i) : V) ∈ (planes.plane i)ᗮ := by
  simp [piP]

theorem inner_piP_left (i : ι) (u : planes.plane i) (v : V) :
    ⟪u, piP planes i v⟫ = ⟪(u : V), v⟫ := by
  simp [piP]

variable [Fintype ι]

theorem sum_proj_apply (v : V) : ∑ i, planes.proj i v = v := by
  have hfam : OrthogonalFamily ℝ (fun i => planes.plane i)
      (fun i => (planes.plane i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise planes.pairwise_orthogonal
  have := hfam.sum_projection_of_mem_iSup v (by rw [planes.exhaustive]; trivial)
  simpa [PlaneDecomposition.proj, Submodule.coe_orthogonalProjectionOnto_apply] using this

theorem sum_proj : ∑ i, planes.proj i = (LinearMap.id : V →ₗ[ℝ] V) := by
  ext v
  simp [LinearMap.sum_apply, sum_proj_apply]

theorem sum_inner_piP (z w : V) : ∑ i, ⟪piP planes i z, piP planes i w⟫ = ⟪z, w⟫ := by
  conv_rhs => rw [← sum_proj_apply planes z]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_piP_left]
  rfl

/-! Facts depending on a cubic with the plane hypotheses. -/

section Cubic

variable (d : SymmetricCubic V)

/-- The compressed slice of a cubic on one plane. -/
def slice (i : ι) (x : V) : Module.End ℝ (planes.plane i) :=
  (planes.restriction i d).L (piP planes i x)

omit [FiniteDimensional ℝ V] [Fintype ι] in
theorem apply_sum {κ : Type*} (s : Finset κ) (c : κ → SymmetricCubic V) (x y z : V) :
    (∑ k ∈ s, c k).apply x y z = ∑ k ∈ s, (c k).apply x y z := by
  simp only [SymmetricCubic.apply, map_sum, LinearMap.sum_apply, sum_inner]

variable {planes d}

omit [Fintype ι] in
/-- Compression of a slice of `d` to a plane, under the repeated-plane rule. -/
theorem compress_slice
    (hrep : ∀ i (x y : planes.plane i) (z : (planes.plane i)ᗮ), d.apply x y z = 0)
    (i : ι) (z : V) :
    piP planes i ∘ₗ d.L z ∘ₗ (planes.plane i).subtype = slice planes d i z := by
  ext u : 1
  apply ext_inner_right ℝ
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, real_inner_comm, inner_piP_left,
    real_inner_comm]
  change d.apply z u v = (planes.restriction i d).apply (piP planes i z) u v
  rw [PlaneDecomposition.restriction_apply]
  have hz := hrep i u v ⟨_, sub_mem_orthogonal planes i z⟩
  have hsplit : z = ((piP planes i z : planes.plane i) : V) +
      (z - ((piP planes i z : planes.plane i) : V)) := by abel
  conv_lhs => rw [hsplit]
  rw [apply_add₁]
  have cyc : ∀ a b c : V, d.apply a b c = d.apply c a b := fun a b c => by
    rw [d.apply_swap₁₂ c, d.apply_swap₂₃]
  rw [cyc] at hz
  rw [hz, add_zero]

/-- The slices of a diagonal cubic assembled from plane pullbacks. -/
theorem L_diagonal {D : SymmetricCubic V} (hD : D = ∑ i, d.pullback (planes.proj i)) (x : V) :
    D.L x = ∑ i, (planes.plane i).subtype ∘ₗ slice planes d i x ∘ₗ piP planes i := by
  ext y : 1
  apply ext_inner_right ℝ
  intro z
  change D.apply x y z = _
  rw [hD, apply_sum, LinearMap.sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pullback_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_subtype,
    ← inner_piP_left]
  change _ = (planes.restriction i d).apply _ _ _
  rw [PlaneDecomposition.restriction_apply]
  rfl

end Cubic

end PlaneContractions

end

end ThirteenPlanes
