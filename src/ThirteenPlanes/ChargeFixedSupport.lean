module

public import ThirteenPlanes.SignedSupport
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! Charges and coefficient sectors for the thirteen-plane product fixed point. -/

namespace ThirteenPlanes
namespace ChargeFixed

/-- The marked projective line is the locus of zero third charge. -/
def onMarkedLine (p : SignedPlaneIndex) : Prop := p.val.val 2 = 0

instance (p : SignedPlaneIndex) : Decidable (onMarkedLine p) :=
  inferInstanceAs (Decidable (p.val.val 2 = 0))

def markedPlanes : Finset SignedPlaneIndex := Finset.univ.filter onMarkedLine

def outsidePlanes : Finset SignedPlaneIndex := Finset.univ.filter (fun p => ¬ onMarkedLine p)

/-- The number of marked planes in a three-plane interaction. -/
def markedCount (s : Finset SignedPlaneIndex) : ℕ := (s.filter onMarkedLine).card

def sectorTriples (n : ℕ) : Finset (Finset SignedPlaneIndex) :=
  signedCollinearTriples.filter fun s => markedCount s = n

abbrev PlaneCoefficient := SignedPlaneIndex
abbrev TripleCoefficient := ↥signedCollinearTriples
abbrev MarkedPlane := ↥markedPlanes
abbrev OutsidePlane := ↥outsidePlanes
abbrev MarkedTriple := ↥(sectorTriples 3)
abbrev OutsideTriple := ↥(sectorTriples 0)
abbrev ReconnectingTriple := ↥(sectorTriples 1)

/-- Real cubics have one complex coefficient per plane and per distinct
collinear triple after taking conjugate pairs of signed grades. -/
abbrev RealCoefficientSpace := (PlaneCoefficient ⊕ TripleCoefficient) → ℂ
abbrev MarkedCoefficients := (MarkedPlane ⊕ MarkedTriple) → ℂ
abbrev OutsideCoefficients := (OutsidePlane ⊕ OutsideTriple) → ℂ
abbrev ReconnectingCoefficients := ReconnectingTriple → ℂ

theorem markedPlanes_card : markedPlanes.card = 4 := by decide +kernel

theorem outsidePlanes_card : outsidePlanes.card = 9 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem markedTriples_card : (sectorTriples 3).card = 4 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem outsideTriples_card : (sectorTriples 0).card = 12 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem reconnectingTriples_card : (sectorTriples 1).card = 36 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem twoMarkedTriples_card : (sectorTriples 2).card = 0 := by decide +kernel

theorem realCoefficientSpace_finrank : Module.finrank ℝ RealCoefficientSpace = 130 := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    Fintype.card_sum,
    Fintype.card_coe, signedPlaneIndex_card, signedCollinearTriples_card]
  decide

theorem markedCoefficients_finrank : Module.finrank ℝ MarkedCoefficients = 16 := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    Fintype.card_sum,
    Fintype.card_coe, Fintype.card_coe, markedPlanes_card, markedTriples_card]
  decide

theorem outsideCoefficients_finrank : Module.finrank ℝ OutsideCoefficients = 42 := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    Fintype.card_sum,
    Fintype.card_coe, Fintype.card_coe, outsidePlanes_card, outsideTriples_card]
  decide

theorem reconnectingCoefficients_finrank : Module.finrank ℝ ReconnectingCoefficients = 72 := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe,
    reconnectingTriples_card]
  decide

end ChargeFixed
end ThirteenPlanes
