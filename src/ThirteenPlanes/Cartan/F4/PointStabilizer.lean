module

public import ThirteenPlanes.FiniteGroup.Transitive
public import ThirteenPlanes.SignedPlanes

@[expose] public section

set_option backward.privateInPublic true

/-! The stabilizer of a ternary grade representative permutes the other twelve real planes
transitively, with an exact choice of sign on each representative. -/

namespace ThirteenPlanes.FiniteGroup

open Matrix

private theorem distinct_representatives_independent {p q : SignedPlaneIndex}
    (hq : q ≠ p) : ¬ dependentGrades p.val.val q.val.val := by
  rintro (hp₀ | hq₀ | heq | hop)
  · exact p.val.property hp₀
  · exact q.val.property hq₀
  · exact hq (Subtype.ext (Subtype.ext heq.symm))
  · have hrep : isChargeRepresentative (oppositeCharge q.val).val := by
      change isChargeRepresentative (-q.val.val)
      rw [← hop]
      exact p.property
    exact (oppositeCharge_isRepresentative_iff q.val).mp hrep q.property

/-- The stabilizer fixes the chosen vector itself and carries the second representative to
the third with its chosen sign. -/
theorem sl_signedPlane_stabilizer_transitive (p q r : SignedPlaneIndex)
    (hq : q ≠ p) (hr : r ≠ p) :
    ∃ A : SpecialLinearGroup (Fin 3) (ZMod 3),
      (A : ChargeMatrix) *ᵥ p.val.val = p.val.val ∧
      (A : ChargeMatrix) *ᵥ q.val.val = r.val.val :=
  sl_transitive_pairs (distinct_representatives_independent hq)
    (distinct_representatives_independent hr)

end ThirteenPlanes.FiniteGroup
