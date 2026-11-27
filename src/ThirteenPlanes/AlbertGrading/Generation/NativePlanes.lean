module

public import ThirteenPlanes.Cartan.FramePlanes
public import ThirteenPlanes.AlbertGrading.Generation.Generation

@[expose] public section

/-! Every closed Albert plane is the plane of a Jordan frame. -/

namespace ThirteenPlanes.AlbertGrading

/-- Each closed native two-plane has an actual Jordan frame. -/
theorem nativeClosedPlaneHasFrame : FrameProperties.ClosedPlaneHasFrame := Cartan.nativeClosedPlane_has_frame

/-- The two-plane generation statement on actual planes. -/
theorem nativeGenerationTwoPlanes : Statements.GenerationTwoPlanes := generationTwoPlanes nativeClosedPlaneHasFrame

/-- The three-plane generation statement on actual planes. -/
theorem nativeGenerationThreePlanes : Statements.GenerationThreePlanes := generationThreePlanes nativeClosedPlaneHasFrame

end ThirteenPlanes.AlbertGrading
