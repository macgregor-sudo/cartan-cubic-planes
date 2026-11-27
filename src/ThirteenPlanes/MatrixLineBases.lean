module

public import ThirteenPlanes.WeylBasis
public import ThirteenPlanes.FourPlanesProjectors

@[expose] public section

namespace ThirteenPlanes
open AlbertSequential
noncomputable section

/-- Identify a qutrit outcome with its Weyl coordinate in (\mathbb Z/3). -/
def qutritResidue (i : Fin 3) : ZMod 3 := i

/-- The ordinary outcome underlying a Weyl coordinate. -/
def qutritIndex (i : ZMod 3) : Fin 3 := i

@[simp] theorem qutritResidue_index (i : ZMod 3) :
    qutritResidue (qutritIndex i) = i := rfl

theorem qutritCharacter_eq_chargePhase (b : Fin 3) :
    qutritCharacter b = chargePhase (qutritResidue b) := by
  have h : qutritRoot = chargeRoot := qutritRoot_eq
  fin_cases b
  · rfl
  · change qutritRoot = chargeRoot ^ 1; simpa using h
  · change star qutritRoot = chargePhase (-(1 : ZMod 3))
    rw [chargePhase_neg, h]
    congr 1
    change chargeRoot = chargeRoot ^ 1
    simp

/-- The three Fourier bases use the quadratic characters on F₃. -/
theorem fourierVector_as_phase (a b i : Fin 3) :
    qutritFourierVector (qutritCharacter a) b i =
      (Real.sqrt (1/3) : ℂ) * chargePhase ((qutritResidue a) *
        (qutritResidue i)^2 + (qutritResidue b) * (qutritResidue i)) := by
  unfold qutritFourierVector
  congr 1
  fin_cases i
  · change (1:ℂ) = chargePhase (qutritResidue a*0^2+qutritResidue b*0)
    simp
  · change qutritCharacter a * qutritCharacter b =
      chargePhase (qutritResidue a*1^2+qutritResidue b*1)
    simp [qutritCharacter_eq_chargePhase, chargePhase_add]
  · change qutritCharacter a * star (qutritCharacter b) =
      chargePhase (qutritResidue a*2^2+qutritResidue b*2)
    rw [qutritCharacter_eq_chargePhase, qutritCharacter_eq_chargePhase, ← chargePhase_neg,
      ← chargePhase_add]
    congr 1
    have h : (2 : ZMod 3) = -1 := by decide
    rw [h]; ring

theorem weylMatrix_mulVec (v : WeylLabel) (f : ZMod 3 → ℂ) (i : ZMod 3) :
    (weylMatrix v).mulVec f i =
      chargePhase (-v.1*v.2+v.2*(i-v.1)) * f (i-v.1) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (i-v.1)]
  · simp [weylMatrix]
  · intro j _ h
    have hij : i ≠ j + v.1 := by intro hij; apply h; rw [hij]; abel
    simp [weylMatrix, hij]
  · simp

/-- The published Fourier vector, expressed as a function on Weyl coordinates. -/
def qutritWeylVector (a b : Fin 3) (i : ZMod 3) : ℂ :=
  qutritFourierVector (qutritCharacter a) b (qutritIndex i)

theorem qutritWeylVector_as_phase (a b : Fin 3) (i : ZMod 3) :
    qutritWeylVector a b i = (Real.sqrt (1 / 3) : ℂ) *
      chargePhase (qutritResidue a * i ^ 2 + qutritResidue b * i) := by
  rw [qutritWeylVector, fourierVector_as_phase, qutritResidue_index]

/-- The Fourier basis indexed by a diagonalizes the Weyl direction (1,2a). -/
theorem fourierVector_weylEigen (a b : Fin 3) :
    (weylMatrix (1, 2 * qutritResidue a)).mulVec (qutritWeylVector a b) =
      chargePhase (-qutritResidue b) • qutritWeylVector a b := by
  funext i
  rw [weylMatrix_mulVec]
  simp only [qutritWeylVector_as_phase, Pi.smul_apply, smul_eq_mul]
  let aa := qutritResidue a
  let bb := qutritResidue b
  change chargePhase (-1*(2*aa)+(2*aa)*(i-1)) *
    ((Real.sqrt (1/3) : ℂ) * chargePhase (aa*(i-1)^2+bb*(i-1))) =
    chargePhase (-bb) * ((Real.sqrt (1/3) : ℂ) * chargePhase (aa*i^2+bb*i))
  rw [mul_left_comm, mul_left_comm (chargePhase (-bb)), ← chargePhase_add, ← chargePhase_add]
  congr 2
  linear_combination -aa * (by decide : (3 : ZMod 3)=0)

end
end ThirteenPlanes
