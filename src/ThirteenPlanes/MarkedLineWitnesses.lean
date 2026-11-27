module

public import ThirteenPlanes.MatrixLine
public import ThirteenPlanes.FourPlanesTwoShare
public import ThirteenPlanes.SignedEnergyShares

@[expose] public section

set_option backward.privateInPublic true

/-! The three literal qutrit projectors under the signed Weyl-line isometry. -/

namespace ThirteenPlanes

noncomputable section

private theorem chargePhase_re_for_corner (a : ZMod 3) :
    (chargePhase a).re = if a = 0 then 1 else -1 / 2 := by
  fin_cases a
  · change (chargeRoot ^ 0).re = 1
    norm_num
  · change (chargeRoot ^ 1).re = -1 / 2
    simp
  · change (chargeRoot ^ 2).re = -1 / 2
    simp [chargeRoot_sq_eq_star]

private theorem matrixLineEmbed_corner_coordinate (k : Fin 4) (b : Fin 3) (z : ℂ)
    (hcoeff : ∀ c : Fin 3, 2 * (z * matrixLineEigenvalue k c).re = matrixCornerCoeff b c) :
    matrixLineEmbed (matrixCorner k b) = signedPlaneInclusion (matrixLineGrade k) z := by
  apply gradedTitsEquiv.injective
  apply Subtype.ext
  apply Tits.CompactTits.ext
  change Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv (matrixLineEmbed (matrixCorner k b))) =
    Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv (signedPlaneInclusion (matrixLineGrade k) z))
  rw [gradedTitsEquiv_matrixLineEmbed, matrixLineTits_coordinates, gradedTitsEquiv_coordinates,
    signedPlaneInclusion_matrixLine_coordinates]
  simp only [matrixCorner, TracelessHermitian3.toMatrix_ofMatrix, hcoeff]

/-- The standard-basis projector corner maps to the signed grade `(0,1,0)` with coordinate `1`. -/
theorem matrixLineEmbed_markedCornerOne : matrixLineEmbed (matrixCorner 0 0) = signedMarkedCornerOne := by
  have hp : matrixLineGrade 0 = signedMarkedPlaneOne := by decide
  rw [signedMarkedCornerOne, ← hp]
  apply matrixLineEmbed_corner_coordinate
  intro c
  change 2 * ((1 : ℂ) * chargePhase (qutritResidue c)).re = matrixCornerCoeff 0 c
  rw [one_mul, chargePhase_re_for_corner]
  have hc : qutritResidue c = 0 ↔ c = 0 := by fin_cases c <;> decide
  simp only [matrixCornerCoeff, hc]
  split_ifs <;> norm_num

/-- The flat-vector projector corner maps to the signed grade `(1,0,0)` with coordinate `1`. -/
theorem matrixLineEmbed_markedCornerTwo : matrixLineEmbed (matrixCorner 1 0) = signedMarkedCornerTwo := by
  have hp : matrixLineGrade 1 = signedMarkedPlaneTwo := by decide
  rw [signedMarkedCornerTwo, ← hp]
  apply matrixLineEmbed_corner_coordinate
  intro c
  change 2 * ((1 : ℂ) * chargePhase (-qutritResidue c)).re = matrixCornerCoeff 0 c
  rw [one_mul, chargePhase_re_for_corner]
  have hc : -qutritResidue c = 0 ↔ c = 0 := by fin_cases c <;> decide
  simp only [matrixCornerCoeff, hc]
  split_ifs <;> norm_num

/-- The `(1,1,ω)` projector corner maps to grade `(1,1,0)` with representative coordinate `ω`. -/
theorem matrixLineEmbed_markedCornerThree : matrixLineEmbed (matrixCorner 3 1) = signedMarkedCornerThree := by
  have hp : matrixLineGrade 3 = signedMarkedPlaneThree := by decide
  rw [signedMarkedCornerThree, ← hp]
  apply matrixLineEmbed_corner_coordinate
  intro c
  change 2 * (chargeRoot * chargePhase (-qutritResidue c)).re = matrixCornerCoeff 1 c
  have hroot : chargePhase 1 = chargeRoot := by change chargeRoot ^ 1 = _; simp
  rw [← hroot, ← chargePhase_add, chargePhase_re_for_corner]
  have hc : 1 + -qutritResidue c = 0 ↔ c = 1 := by fin_cases c <;> decide
  simp only [matrixCornerCoeff, hc]
  split_ifs <;> norm_num

/-- The three normalized matrix witnesses are the actual signed witnesses used in the energy tests. -/
theorem matrixLineEmbed_markedWitnesses :
    matrixLineEmbed fourPlaneMarkedOne = signedMarkedOne ∧
    matrixLineEmbed fourPlaneMarkedTwo = signedMarkedTwo ∧
    matrixLineEmbed fourPlaneMarkedThree = signedMarkedThree := by
  have h₁ : matrixLineEmbed fourPlaneMarkedOne = signedMarkedOne := by
    simp [fourPlaneMarkedOne, signedMarkedOne, matrixLineEmbed_markedCornerOne]
  refine ⟨h₁, ?_, ?_⟩
  · simp [fourPlaneMarkedTwo, matrixTwoShare, signedMarkedTwo, signedTwoShare, h₁,
      matrixLineEmbed_markedCornerTwo]
  · simp [fourPlaneMarkedThree, markedCornerTriple, signedMarkedThree, signedMarkedCornerTriple,
      matrixLineEmbed_markedCornerOne, matrixLineEmbed_markedCornerTwo, matrixLineEmbed_markedCornerThree]


/-- The three constituents of the marked witnesses lie in the prescribed matrix and signed planes. -/
theorem markedCorners_plane_membership :
    matrixCorner 0 0 ∈ matrixPlane 0 ∧ matrixCorner 1 0 ∈ matrixPlane 1 ∧
      matrixCorner 3 1 ∈ matrixPlane 3 ∧
      signedMarkedCornerOne ∈ signedPlane signedMarkedPlaneOne ∧
      signedMarkedCornerTwo ∈ signedPlane signedMarkedPlaneTwo ∧
      signedMarkedCornerThree ∈ signedPlane signedMarkedPlaneThree :=
  ⟨(mem_matrixPlane_iff 0 _).mpr (matrixCorner_fixed 0 0),
    (mem_matrixPlane_iff 1 _).mpr (matrixCorner_fixed 1 0),
    (mem_matrixPlane_iff 3 _).mpr (matrixCorner_fixed 3 1),
    ⟨1, rfl⟩, ⟨1, rfl⟩, ⟨chargeRoot, rfl⟩⟩

end

end ThirteenPlanes
