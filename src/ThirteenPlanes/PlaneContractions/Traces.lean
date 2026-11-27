module

public import ThirteenPlanes.PlaneContractions.Planes

@[expose] public section

/-! Trace identities for the diagonal cubic and the equal-strength cubic under the plane hypotheses
and the square law. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace PlaneContractions

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} {planes : PlaneDecomposition V ι} {d : SymmetricCubic V}

/-- The square law restricts to each plane under the repeated-plane rule. -/
theorem restriction_squareLaw
    (hrep : ∀ i (x y : planes.plane i) (z : (planes.plane i)ᗮ), d.apply x y z = 0)
    (hsq : HasSquareLaw d) (i : ι) : HasSquareLaw (planes.restriction i d) := by
  intro u
  have hc := LinearMap.congr_fun (compress_slice hrep i (u : V)) u
  have hu : piP planes i (u : V) = u := LinearMap.congr_fun (piP_subtype planes i) u
  simp only [LinearMap.comp_apply, Submodule.coe_subtype, slice, hu] at hc
  have hmem : d.L u u ∈ planes.plane i := by
    apply (Submodule.orthogonal_orthogonal (K := planes.plane i)).le
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [real_inner_comm]
    exact hrep i u u ⟨w, hw⟩
  change ‖(planes.restriction i d).L u u‖ ^ 2 = _
  rw [← hc]
  have hn : ‖piP planes i (d.L u u)‖ = ‖d.L u u‖ :=
    Submodule.norm_orthogonalProjectionOnto_apply (planes.plane i) hmem
  rw [hn]
  exact hsq u

variable [Fintype ι]

/-- Traces against the diagonal cubic split into traces on the planes. -/
theorem trace_diag_mul {D : SymmetricCubic V} (hD : D = ∑ i, d.pullback (planes.proj i))
    (x : V) (Y : Module.End ℝ V) :
    LinearMap.trace ℝ V (D.L x * Y) =
      ∑ i, LinearMap.trace ℝ (planes.plane i)
        (slice planes d i x * (piP planes i ∘ₗ Y ∘ₗ (planes.plane i).subtype)) := by
  rw [L_diagonal hD, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc, LinearMap.comp_assoc,
    LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

theorem piP_comp_L_diag {D : SymmetricCubic V} (hD : D = ∑ i, d.pullback (planes.proj i))
    (i : ι) (y : V) : piP planes i ∘ₗ D.L y = slice planes d i y ∘ₗ piP planes i := by
  classical
  ext v : 1
  rw [L_diagonal hD, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    Finset.sum_eq_single i]
  · exact LinearMap.congr_fun (piP_subtype planes i) _
  · intro j _ hji
    exact LinearMap.congr_fun (piP_subtype_ne planes (Ne.symm hji)) _
  · intro h; exact absurd (Finset.mem_univ i) h

end PlaneContractions

end

end ThirteenPlanes
