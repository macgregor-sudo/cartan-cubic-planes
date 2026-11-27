module

public import ThirteenPlanes.FieldDefect.FieldsCount
public import ThirteenPlanes.FieldDefect.Main

@[expose] public section

/-! The defect proposition with the native field count supplied by its proved theorem. -/

namespace ThirteenPlanes.AlbertGrading

/-- All three defect bounds, including attainment and positivity. -/
theorem nativeFieldDefectAndFrameGap :
    Statements.DefectAttained ∧ Statements.DefectSeven ∧ Statements.SixFramesGap :=
  propDefect Defect.fieldsCount

end ThirteenPlanes.AlbertGrading
