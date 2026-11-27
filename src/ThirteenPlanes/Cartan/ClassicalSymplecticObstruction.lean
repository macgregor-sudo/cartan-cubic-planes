module

public import ThirteenPlanes.Cartan.ClassicalQuaternionicObstruction
public import ThirteenPlanes.Cartan.ClassicalSymplecticDescent

@[expose] public section

/-! The compact-form compatible obstruction in complex sp(6). -/

namespace ThirteenPlanes.Cartan

noncomputable section

/-- The complex symplectic obstruction with compact conjugation. No seven-Cartan Killing-orthogonal decomposition of the
actual complex symplectic matrices is permuted by any compact conjugation. -/
theorem no_sp6C_OD_permuted_by_compactConjugation :
    ¬ ∃ (H : Fin 7 → LieSubalgebra ℂ complexSp6) (σ : LieConjugation complexSp6) (π : Equiv.Perm (Fin 7)),
      IsKillingCartanOD H ∧ σ.IsCompact ∧ ∀ i, σ '' (H i : Set complexSp6) = H (π i) :=
  fun h => no_compactSp3_cartanOD (compactSp3_cartanOD_iff_complex_compatible.mpr h)

end
end ThirteenPlanes.Cartan
