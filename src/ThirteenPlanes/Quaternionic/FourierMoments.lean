module

public import ThirteenPlanes.Quaternionic.Fourier
public import ThirteenPlanes.Quaternionic.Heron

@[expose] public section

/-!
# Small exact Fourier moment identities

The mixed real character uses the bijection (b,c)↦(c-b,-c-b) on three residues.
Keeping these linear moments separate avoids expanding the full native quartic
weight into one large quaternion-coordinate proof term.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

def complexPhase (i : Outcome) : ℂ :=
  ![1, ⟨-1/2, Real.sqrt 3/2⟩, ⟨-1/2, -Real.sqrt 3/2⟩] i

def fourierDifference (b c : Outcome) : Outcome :=
  (!![0,1,2; 2,0,1; 1,2,0] : Matrix Outcome Outcome Outcome) b c

def fourierNegativeSum (b c : Outcome) : Outcome :=
  (!![0,2,1; 2,1,0; 1,0,2] : Matrix Outcome Outcome Outcome) b c

def mixedFourierRe (z w : ℂ) (b c : Outcome) : ℝ :=
  (z*complexPhase (fourierDifference b c)+
    w*complexPhase (fourierNegativeSum b c)).re

lemma mixedFourierRe_add (z z' w w' : ℂ) (b c : Outcome) :
    mixedFourierRe (z+z') (w+w') b c=
      mixedFourierRe z w b c+mixedFourierRe z' w' b c := by
  simp only [mixedFourierRe, add_mul, Complex.add_re]
  ring

lemma mixedFourierRe_sum (z w : ℂ) :
    ∑ b, ∑ c, mixedFourierRe z w b c=0 := by
  simp [mixedFourierRe, complexPhase, fourierDifference, fourierNegativeSum,
    Fin.sum_univ_succ, Complex.mul_re]
  <;> ring

lemma mixedFourierRe_sum_sq (z w : ℂ) :
    ∑ b, ∑ c, (mixedFourierRe z w b c)^2=
      (9/2:ℝ)*(Complex.normSq z+Complex.normSq w) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  simp [mixedFourierRe, complexPhase, fourierDifference, fourierNegativeSum,
    Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply]
  ring_nf
  norm_num [hs]
  <;> ring

lemma mixedFourierRe_affine_sum_sq (n t : ℝ) (z w : ℂ) :
    ∑ b, ∑ c, (n+t*mixedFourierRe z w b c)^2=
      9*n^2+(9/2:ℝ)*t^2*(Complex.normSq z+Complex.normSq w) := by
  calc
    _ = 9*n^2+2*n*t*(∑ b, ∑ c, mixedFourierRe z w b c)+
        t^2*(∑ b, ∑ c, (mixedFourierRe z w b c)^2) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring
    _ = _ := by rw [mixedFourierRe_sum, mixedFourierRe_sum_sq]; ring

lemma complex_three_pair_norms (x y z : ℂ) :
    Complex.normSq (x+y)+Complex.normSq (x+z)+Complex.normSq (y+z)=
      Complex.normSq x+Complex.normSq y+Complex.normSq z+Complex.normSq (x+y+z) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

end QuaternionicMUB
