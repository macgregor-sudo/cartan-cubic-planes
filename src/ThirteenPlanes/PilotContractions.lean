module

public import ThirteenPlanes.FourPlanesPlaneData
public import ThirteenPlanes.PlaneContractions

@[expose] public section

namespace ThirteenPlanes

noncomputable section

/-- The real traceless Hermitian carrier of the matrix control has dimension eight. -/
theorem fourPlane_dimension : Module.finrank ℝ TracelessHermitian3 = 8 := by
  have h := matrixPlane_iSup_finrank
  rwa [matrixPlane_exhaustive, finrank_top] at h

/-- Both contractions for the actual cubics on the four specified matrix frames. -/
theorem fourPlane_contractionLaws : HasContractionLaws fourPlanePair (1/2 : ℝ) := by
  have h := planeContractionLaws fourPlanePair fourPlaneDecomposition fourPlaneData fourPlane_squareLaw
  rw [fourPlane_dimension] at h
  norm_num at h
  exact h

end
end ThirteenPlanes
