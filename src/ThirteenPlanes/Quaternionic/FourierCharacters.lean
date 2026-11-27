module

public import ThirteenPlanes.Quaternionic.QuaternionComplex

@[expose] public section

/-! Finite complex character arithmetic for the actual Fourier phase entries. -/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

def phaseAdd (i j : Outcome) : Outcome :=
  (!![0,1,2; 1,2,0; 2,0,1] : Matrix Outcome Outcome Outcome) i j

def phaseNeg (i : Outcome) : Outcome := ![0,2,1] i

def phaseProductIndex (i j : Outcome) : Outcome :=
  (!![0,0,0; 0,1,2; 0,2,1] : Matrix Outcome Outcome Outcome) i j

def complexFourierEntry (i j : Outcome) : ℂ := complexPhase (phaseProductIndex i j)

def edgeStart (j : Outcome) : Outcome := ![0,2,1] j

def edgeEnd (j : Outcome) : Outcome := ![1,0,2] j

lemma complexPhase_mul (i j : Outcome) :
    complexPhase i*complexPhase j=complexPhase (phaseAdd i j) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [complexPhase, phaseAdd, Complex.mul_re, Complex.mul_im] <;> nlinarith


lemma complexPhase_star (i : Outcome) : star (complexPhase i)=complexPhase (phaseNeg i) := by
  fin_cases i <;> apply Complex.ext <;> simp [complexPhase, phaseNeg, Complex.star_def] <;> ring


lemma fourierPhaseMatrix_complex (i j : Outcome) :
    fourierPhaseMatrix i j=quaternionOfComplexPair (complexFourierEntry i j) 0 := by
  fin_cases i <;> fin_cases j <;> ext <;>
    simp [fourierPhaseMatrix, complexFourierEntry, phaseProductIndex,
      complexPhase, quaternionOfComplexPair, omega] <;> ring


lemma cyclic_index_difference (j b c : Outcome) :
    phaseAdd
      (phaseAdd (phaseProductIndex (edgeStart j) b) (phaseNeg (phaseProductIndex (edgeEnd j) b)))
      (phaseAdd (phaseProductIndex (edgeEnd j) c) (phaseNeg (phaseProductIndex (edgeStart j) c)))=
      fourierDifference b c := by
  revert j b c
  decide


lemma cyclic_index_negativeSum (j b c : Outcome) :
    phaseAdd
      (phaseAdd (phaseProductIndex (edgeStart j) b) (phaseNeg (phaseProductIndex (edgeEnd j) b)))
      (phaseNeg (phaseAdd (phaseProductIndex (edgeEnd j) c)
        (phaseNeg (phaseProductIndex (edgeStart j) c))))=
      fourierNegativeSum b c := by
  revert j b c
  decide


lemma cyclic_character_difference (j b c : Outcome) :
    (complexFourierEntry (edgeStart j) b*star (complexFourierEntry (edgeEnd j) b))*
      (complexFourierEntry (edgeEnd j) c*star (complexFourierEntry (edgeStart j) c))=
      complexPhase (fourierDifference b c) := by
  simp only [complexFourierEntry, complexPhase_star, complexPhase_mul]
  rw [cyclic_index_difference]


lemma cyclic_character_negativeSum (j b c : Outcome) :
    (complexFourierEntry (edgeStart j) b*star (complexFourierEntry (edgeEnd j) b))*
      star (complexFourierEntry (edgeEnd j) c*star (complexFourierEntry (edgeStart j) c))=
      complexPhase (fourierNegativeSum b c) := by
  simp only [complexFourierEntry, complexPhase_star, complexPhase_mul]
  rw [cyclic_index_negativeSum]


lemma cyclic_character_mixed (z w : ℂ) (j b c : Outcome) :
    ((complexFourierEntry (edgeStart j) b*star (complexFourierEntry (edgeEnd j) b))*
      (z*(complexFourierEntry (edgeEnd j) c*star (complexFourierEntry (edgeStart j) c))+
       w*star (complexFourierEntry (edgeEnd j) c*star (complexFourierEntry (edgeStart j) c)))).re=
      mixedFourierRe z w b c := by
  unfold mixedFourierRe
  congr 1
  calc
    _ = z*((complexFourierEntry (edgeStart j) b*star (complexFourierEntry (edgeEnd j) b))*
          (complexFourierEntry (edgeEnd j) c*star (complexFourierEntry (edgeStart j) c)))+
        w*((complexFourierEntry (edgeStart j) b*star (complexFourierEntry (edgeEnd j) b))*
          star (complexFourierEntry (edgeEnd j) c*star (complexFourierEntry (edgeStart j) c))) := by ring
    _ = _ := by rw [cyclic_character_difference, cyclic_character_negativeSum]


end QuaternionicMUB
