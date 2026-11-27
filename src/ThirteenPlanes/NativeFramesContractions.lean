/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.NativeFramesPlaneData
public import ThirteenPlanes.PlaneContractions
public import ThirteenPlanes.Reduction

@[expose] public section

/-! The families of thirteen-frame codes on every native tight 39-point code. -/

noncomputable section

namespace ThirteenPlanes

/-- The double and triangle contractions for the homogeneous family of an
arbitrary complementary thirteen-frame code in the compact Albert algebra. -/
theorem tightCode_cubic_contractions (c : TightNativeCode) :
    HasContractionLaws c.cubicPair 2 := by
  have h := planeContractionLaws c.cubicPair c.decomposition c.planeData c.squareLaw
  rw [nativeTraceless_finrank] at h
  norm_num at h
  exact h

/-- On this same native cubic family the one-loop tensor equation restricts to
the homogeneous scalar field with (lambda=2). -/
theorem tightCode_oneLoop_restricts (c : TightNativeCode) (ε : ℝ) (u : ℝ × ℝ) :
    oneLoopBeta ε (coupling c.cubicPair u) = coupling c.cubicPair (familyField 2 ε u) :=
  oneLoop_restricts_to_familyField c.cubicPair (tightCode_cubic_contractions c) u

end ThirteenPlanes
