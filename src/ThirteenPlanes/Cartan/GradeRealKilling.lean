module

public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition

@[expose] public section

/-! Killing form of a Lie algebra split into homogeneous components. -/

namespace ThirteenPlanes.Cartan

open LieAlgebra Module

noncomputable section

variable {Γ E : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
variable [AddCommGroup E] [Module ℂ E] [Module.Finite ℂ E]

/-- A nonzero shift of the grading contributes no diagonal entries to the trace. -/
theorem trace_eq_zero_of_gradeShift (W : Γ → Submodule ℂ E) (hW : DirectSum.IsInternal W)
    (f : Module.End ℂ E) (d : Γ) (hd : d ≠ 0)
    (hf : ∀ g x, x ∈ W g → f x ∈ W (g + d)) : LinearMap.trace ℂ E f = 0 := by
  classical
  let b (g : Γ) := Module.Free.chooseBasis ℂ (W g)
  let B := hW.collectedBasis b
  rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace]
  apply Finset.sum_eq_zero
  rintro ⟨g, i⟩ _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply hW.collectedBasis_repr_of_mem_ne b
  · exact fun h => hd (add_left_cancel (h.trans (add_zero g).symm))
  · exact hf g _ (hW.collectedBasis_mem b ⟨g, i⟩)

variable {G : Type*} [LieRing G] [LieAlgebra ℂ G] [Module.Finite ℂ G]

/-- Two homogeneous elements pair to zero for the actual Killing form unless
their degrees add to zero. -/
theorem killing_eq_zero_of_grade (W : Γ → Submodule ℂ G) (hW : DirectSum.IsInternal W)
    (hLie : ∀ g h x y, x ∈ W g → y ∈ W h → ⁅x, y⁆ ∈ W (g + h))
    {g h : Γ} {x y : G} (hx : x ∈ W g) (hy : y ∈ W h) (hgh : g + h ≠ 0) :
    killingForm ℂ G x y = 0 := by
  change LinearMap.trace ℂ G ((LieModule.toEnd ℂ G G x).comp (LieModule.toEnd ℂ G G y)) = 0
  apply trace_eq_zero_of_gradeShift W hW _ (g + h) hgh
  intro k z hz
  change ⁅x, ⁅y, z⁆⁆ ∈ W (k + (g + h))
  rw [show k + (g + h) = g + (h + k) by abel]
  exact hLie g (h + k) x _ hx (hLie h k y z hy hz)

/-- Distinct opposite-degree pairs are Killing-orthogonal on the whole pair spaces. -/
theorem killing_orthogonal_gradePairs (W : Γ → Submodule ℂ G) (hW : DirectSum.IsInternal W)
    (hLie : ∀ g h x y, x ∈ W g → y ∈ W h → ⁅x, y⁆ ∈ W (g + h))
    {g h : Γ} (hne : g ≠ h) (hneg : g ≠ -h)
    {x y : G} (hx : x ∈ W g ⊔ W (-g)) (hy : y ∈ W h ⊔ W (-h)) :
    killingForm ℂ G x y = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  have hz (r s : Γ) (h : r ≠ -s) : r + s ≠ 0 := fun he => h (eq_neg_of_add_eq_zero_left he)
  have h₁ := killing_eq_zero_of_grade W hW hLie ha hc (hz g h hneg)
  have h₂ := killing_eq_zero_of_grade W hW hLie ha hd (hz g (-h) (by simpa using hne))
  have h₃ := killing_eq_zero_of_grade W hW hLie hb hc
    (hz (-g) h (fun he => hne (neg_injective he)))
  have h₄ := killing_eq_zero_of_grade W hW hLie hb hd
    (hz (-g) (-h) (fun he => hneg (neg_injective he)))
  simp only [map_add, LinearMap.add_apply, h₁, h₂, h₃, h₄, add_zero]

end

end ThirteenPlanes.Cartan
