module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace ThirteenPlanes

abbrev Charge := Fin 3 → ZMod 3
abbrev NonzeroCharge := {x : Charge // x ≠ 0}

def oppositeCharge (x : NonzeroCharge) : NonzeroCharge := ⟨-x.val, neg_ne_zero.mpr x.property⟩

@[simp] theorem oppositeCharge_opposite (x : NonzeroCharge) :
    oppositeCharge (oppositeCharge x) = x := by
  apply Subtype.ext
  exact neg_neg _

/-- The real locus of the charge coordinates, using both members of each opposite pair. -/
def signedFields : Submodule ℝ (NonzeroCharge → ℂ) where
  carrier := {z | ∀ x, z (oppositeCharge x) = star (z x)}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro a b ha hb x
    change a _ + b _ = star (a x + b x)
    rw [ha x, hb x, star_add]
  smul_mem' := by
    intro r a ha x
    change r • a _ = star (r • a x)
    rw [ha x, star_smul]
    simp

/-- Real trace and complexified trace agree on the same real operator. -/
theorem trace_complexification {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] V) :
    LinearMap.trace ℂ _ (f.baseChange ℂ) = algebraMap ℝ ℂ (LinearMap.trace ℝ V f) :=
  LinearMap.trace_baseChange f ℂ

end ThirteenPlanes
