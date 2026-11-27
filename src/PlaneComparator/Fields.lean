/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PlaneComparator.Models

@[expose] public section

/-! Theorem A(i) on the challenge's literal real gradient and trace cubics. -/

namespace Challenge

theorem fields_classification {m : ℕ} (hm : 1 ≤ m) (T : IncreasingTriple m → RealTrilinear)
    (hT : RadialFieldEnergy T) :
    m = 1 ∨ (m = 4 ∧ ComplexCartanForm (fieldPolynomial T) (Real.sqrt 6)) ∨
      (m = 13 ∧ AlbertCartanForm (fieldPolynomial T) (Real.sqrt 6)) :=
  Bridge.field_classification hm T hT

theorem fields_realizations :
    (∃ T : IncreasingTriple 4 → RealTrilinear, RadialFieldEnergy T) ∧
      (∃ T : IncreasingTriple 13 → RealTrilinear, RadialFieldEnergy T) :=
  Bridge.field_witnesses

end Challenge
