/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Graded.Characters

@[expose] public section

/-! The native compact Albert automorphisms of the ternary grading. -/

namespace ThirteenPlanes.Cartan

noncomputable section

/-- Every charge action is an actual compact Albert automorphism. -/
def nativeChargeAutomorphism (s : Charge) : Glennie.CompactAutomorphism where
  equiv := Graded.nativeCharacterAction s
  map_jordan := Graded.nativeCharacterAction_product s
  map_trace := Graded.nativeCharacterAction_trace s

end

end ThirteenPlanes.Cartan
