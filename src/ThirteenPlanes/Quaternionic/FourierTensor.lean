module

public import ThirteenPlanes.Quaternionic.FourierCharacters
public import ThirteenPlanes.Quaternionic.FourierTensorScale

@[expose] public section

/-!
# The 27 native cubic entries from three cyclic edge traces

The real cross term is symmetric in its two coordinate indices. Its three
oriented edges are the three complex characters. This derivation uses native
quaternion multiplication throughout and never expands one large quartic term.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

def rankOneCross (g h : QVec) (a m : Outcome) : ℝ :=
  (g a*star (g m)*h m*star (h a)).re

lemma rankOneCross_symm (g h : QVec) (a m : Outcome) :
    rankOneCross g h a m=rankOneCross g h m a := by
  calc
    _=((g a*star (g m))*(h m*star (h a))).re := by simp only [rankOneCross, mul_assoc]
    _=((h m*star (h a))*(g a*star (g m))).re := quaternion_re_mul_comm _ _
    _=(star ((g m*star (g a))*(h a*star (h m)))).re := by
      simp only [star_mul, star_star]
    _=((g m*star (g a))*(h a*star (h m))).re := Quaternion.re_star _
    _=_ := by simp only [rankOneCross, mul_assoc]

lemma rankOneCross_diag (g h : QVec) (a : Outcome) :
    rankOneCross g h a a=Quaternion.normSq (g a)*Quaternion.normSq (h a) := by
  calc
    _=((g a*star (g a))*(h a*star (h a))).re := by simp only [rankOneCross, mul_assoc]
    _=_ := by rw [Quaternion.self_mul_star, Quaternion.self_mul_star,
      ← Quaternion.coe_mul, Quaternion.re_coe]

def nativeFourierCross (p : Outcome → Q) (a m b c : Outcome) : ℝ :=
  rankOneCross (unscaledFourierColumn b) (unscaledPhasedFourierColumn p c) a m

lemma nativeFourierCross_symm (p : Outcome → Q) (a m b c : Outcome) :
    nativeFourierCross p a m b c=nativeFourierCross p m a b c := rankOneCross_symm _ _ _ _

lemma fourierPhaseMatrix_normSq (i j : Outcome) : Quaternion.normSq (fourierPhaseMatrix i j)=1 := by
  have h := fourierMatrix_entry_normSq i j
  change Quaternion.normSq (fourierScale • fourierPhaseMatrix i j)=(1/3:ℝ) at h
  rw [Quaternion.normSq_smul, pow_two, fourierScale_square] at h
  linarith

lemma nativeFourierCross_diag (p : Outcome → Q) (a b c : Outcome) :
    nativeFourierCross p a a b c=Quaternion.normSq (p a) := by
  rw [nativeFourierCross, rankOneCross_diag]
  simp only [unscaledFourierColumn, unscaledPhasedFourierColumn, map_mul,
    fourierPhaseMatrix_normSq, one_mul, mul_one]

lemma nativeFourierCross_complex (p : Outcome → Q) (a m b c : Outcome) :
    nativeFourierCross p a m b c=
      ((complexFourierEntry a b*star (complexFourierEntry m b))*
        (quaternionComplexPart (p m)*star (quaternionComplexPart (p a))*
            (complexFourierEntry m c*star (complexFourierEntry a c))+
         quaternionJPart (p m)*star (quaternionJPart (p a))*
            star (complexFourierEntry m c*star (complexFourierEntry a c)))).re := by
  unfold nativeFourierCross rankOneCross unscaledFourierColumn unscaledPhasedFourierColumn
  simp only [fourierPhaseMatrix_complex, star_mul, quaternionComplex_star]
  calc
    _=(quaternionOfComplexPair (complexFourierEntry a b*star (complexFourierEntry m b)) 0*
        p m*quaternionOfComplexPair (complexFourierEntry m c*star (complexFourierEntry a c)) 0*
        star (p a)).re := by
      rw [← quaternionComplex_mul, ← quaternionComplex_mul]
      simp only [mul_assoc]
    _=_ := by
      simpa only [star_mul, star_star] using (quaternion_complex_edge
        (complexFourierEntry a b*star (complexFourierEntry m b))
        (complexFourierEntry m c*star (complexFourierEntry a c)) (p m) (p a))

lemma phaseEdgesA_eq (p : Outcome → Q) (j : Outcome) :
    phaseEdgesA p j=quaternionComplexPart (p (edgeEnd j))*
      star (quaternionComplexPart (p (edgeStart j))) := by
  fin_cases j <;> rfl

lemma phaseEdgesB_eq (p : Outcome → Q) (j : Outcome) :
    phaseEdgesB p j=quaternionJPart (p (edgeEnd j))*
      star (quaternionJPart (p (edgeStart j))) := by
  fin_cases j <;> rfl

lemma nativeFourierCross_cyclic (p : Outcome → Q) (j b c : Outcome) :
    nativeFourierCross p (edgeStart j) (edgeEnd j) b c=
      mixedFourierRe (phaseEdgesA p j) (phaseEdgesB p j) b c := by
  rw [nativeFourierCross_complex, phaseEdgesA_eq, phaseEdgesB_eq]
  exact cyclic_character_mixed _ _ j b c

lemma nativeFourierCross_row (p : Outcome → Q) (a b c : Outcome) :
    (∑ m, nativeFourierCross p a m b c)=Quaternion.normSq (p a)+
      mixedFourierRe (phaseEdgesA p (firstIncident a)) (phaseEdgesB p (firstIncident a)) b c+
      mixedFourierRe (phaseEdgesA p (secondIncident a)) (phaseEdgesB p (secondIncident a)) b c := by
  have h01 : nativeFourierCross p 0 1 b c=mixedFourierRe (phaseEdgesA p 0) (phaseEdgesB p 0) b c :=
    nativeFourierCross_cyclic p 0 b c
  have h20 : nativeFourierCross p 2 0 b c=mixedFourierRe (phaseEdgesA p 1) (phaseEdgesB p 1) b c :=
    nativeFourierCross_cyclic p 1 b c
  have h12 : nativeFourierCross p 1 2 b c=mixedFourierRe (phaseEdgesA p 2) (phaseEdgesB p 2) b c :=
    nativeFourierCross_cyclic p 2 b c
  have h10 := (nativeFourierCross_symm p 1 0 b c).trans h01
  have h02 := (nativeFourierCross_symm p 0 2 b c).trans h20
  have h21 := (nativeFourierCross_symm p 2 1 b c).trans h12
  fin_cases a <;>
    simp [Fin.sum_univ_succ, nativeFourierCross_diag, h01, h20, h12, h10, h02, h21,
      firstIncident, secondIncident] <;> ring

lemma fourier_tensor_sum_cross (p : Outcome → Q) (a b c : Outcome) :
    centeredTensor QBasis.coordinate.point fourierBasis.point
      (fun j => projector (phasedFourierColumn p j)) a b c=
      ((∑ m, nativeFourierCross p a m b c)-1)/9 := by
  rw [fourier_tensor_scale]
  have hsum : unscaledFourierColumn b a*
      qInner (unscaledFourierColumn b) (unscaledPhasedFourierColumn p c)*
      star (unscaledPhasedFourierColumn p c a)=
      ∑ m, unscaledFourierColumn b a*star (unscaledFourierColumn b m)*
        unscaledPhasedFourierColumn p c m*star (unscaledPhasedFourierColumn p c a) := by
    simp only [qInner, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [hsum, quaternion_re_sum]
  rfl

/-- Every literal centered cubic entry is the corresponding pair of edge characters. -/
theorem phased_fourier_tensor_entry (p : Outcome → Q) (a b c : Outcome) :
    centeredTensor QBasis.coordinate.point fourierBasis.point
      (fun j => projector (phasedFourierColumn p j)) a b c =
      (Quaternion.normSq (p a)-1+
        mixedFourierRe (phaseEdgesA p (firstIncident a)) (phaseEdgesB p (firstIncident a)) b c+
        mixedFourierRe (phaseEdgesA p (secondIncident a)) (phaseEdgesB p (secondIncident a)) b c)/9 := by
  rw [fourier_tensor_sum_cross, nativeFourierCross_row]
  ring

end QuaternionicMUB
