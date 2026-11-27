module

public import ThirteenPlanes.Quaternionic.FourierCoordinateDefs

@[expose] public section

/-! Remove the common normalization before native coordinate algebra. -/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

def fourierPhaseMatrix : QMat := !![1,1,1; 1,omega,star omega; 1,star omega,omega]

def unscaledFourierColumn (b : Outcome) : QVec := fun i => fourierPhaseMatrix i b

def unscaledPhasedFourierColumn (p : Outcome → Q) (c : Outcome) : QVec :=
  fun i => p i*fourierPhaseMatrix i c

lemma qInner_smul_both (r s : ℝ) (u v : QVec) :
    qInner (r • u) (s • v)=(r*s) • qInner u v := by
  simp only [qInner, Pi.smul_apply, star_smul, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul, ← Finset.smul_sum]
  rw [mul_comm s r]

lemma fourierScale_square : fourierScale*fourierScale=(1/3:ℝ) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  dsimp [fourierScale]
  nlinarith

lemma fourierBasis_column_scale (b : Outcome) :
    fourierBasis.column b=fourierScale • unscaledFourierColumn b := rfl

lemma phasedFourier_column_scale (p : Outcome → Q) (c : Outcome) :
    phasedFourierColumn p c=fourierScale • unscaledPhasedFourierColumn p c := by
  funext i
  change p i*(fourierScale • fourierPhaseMatrix i c)=
    fourierScale • (p i*fourierPhaseMatrix i c)
  rw [mul_smul_comm]

lemma fourier_overlap_scale (p : Outcome → Q) (b c : Outcome) :
    qInner (fourierBasis.column b) (phasedFourierColumn p c)=
      (1/3:ℝ) • qInner (unscaledFourierColumn b) (unscaledPhasedFourierColumn p c) := by
  rw [fourierBasis_column_scale, phasedFourier_column_scale,
    qInner_smul_both, fourierScale_square]

lemma fourier_overlap_norm_scale (p : Outcome → Q) (b c : Outcome) :
    Quaternion.normSq (qInner (fourierBasis.column b) (phasedFourierColumn p c))=
      Quaternion.normSq (qInner (unscaledFourierColumn b)
        (unscaledPhasedFourierColumn p c))/9 := by
  rw [fourier_overlap_scale, Quaternion.normSq_smul]
  ring

end QuaternionicMUB
