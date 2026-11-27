module

public import ThirteenPlanes.Quaternionic.FourierMoments

@[expose] public section

/-! Literal native Fourier columns and their complex coordinate expressions. -/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

/-- The actual complex coefficients of p=a+bj in the fixed quaternion basis. -/
def phaseA (p : Outcome → Q) (i : Outcome) : ℂ := ⟨(p i).re, (p i).imI⟩
def phaseB (p : Outcome → Q) (i : Outcome) : ℂ := ⟨(p i).imJ, (p i).imK⟩

def phaseCorrelationEnergy (p : Outcome → Q) : ℝ :=
  Complex.normSq (Heron.correlation (phaseA p)) +
    Complex.normSq (Heron.correlation (phaseB p))

def phasePairEnergy (p : Outcome → Q) : ℝ :=
  Complex.normSq (phaseA p 0)*Complex.normSq (phaseA p 1) +
  Complex.normSq (phaseA p 1)*Complex.normSq (phaseA p 2) +
  Complex.normSq (phaseA p 2)*Complex.normSq (phaseA p 0) +
  Complex.normSq (phaseB p 0)*Complex.normSq (phaseB p 1) +
  Complex.normSq (phaseB p 1)*Complex.normSq (phaseB p 2) +
  Complex.normSq (phaseB p 2)*Complex.normSq (phaseB p 0)

def phasedFourierColumn (p : Outcome → Q) (c : Outcome) : QVec :=
  fun i => p i * fourierMatrix i c

def fourierOverlapVariance (p : Outcome → Q) : ℝ :=
  ∑ b, ∑ c, (Quaternion.normSq
    (qInner (fourierBasis.column b) (phasedFourierColumn p c)) - 1/3)^2

def rawPhasedFourierS (p : Outcome → Q) : ℝ :=
  6 * w QBasis.coordinate.point fourierBasis.point
    (fun c => projector (phasedFourierColumn p c))

lemma phase_normSq_split (p : Outcome → Q) (i : Outcome) :
    Complex.normSq (phaseA p i)+Complex.normSq (phaseB p i) = Quaternion.normSq (p i) := by
  simp only [phaseA, phaseB, Complex.normSq_apply, Quaternion.normSq_def']
  ring

def phaseEdgesA (p : Outcome → Q) : Outcome → ℂ :=
  ![phaseA p 1*star (phaseA p 0), phaseA p 0*star (phaseA p 2),
    phaseA p 2*star (phaseA p 1)]

def phaseEdgesB (p : Outcome → Q) : Outcome → ℂ :=
  ![phaseB p 1*star (phaseB p 0), phaseB p 0*star (phaseB p 2),
    phaseB p 2*star (phaseB p 1)]

def firstIncident (a : Outcome) : Outcome := ![0,0,1] a

def secondIncident (a : Outcome) : Outcome := ![1,2,2] a


end QuaternionicMUB
