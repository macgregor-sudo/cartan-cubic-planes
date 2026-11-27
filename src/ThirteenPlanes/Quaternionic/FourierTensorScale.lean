module

public import ThirteenPlanes.Quaternionic.TripleTrace
public import ThirteenPlanes.Quaternionic.FourierScale

@[expose] public section

/-! The native tensor scaling bridge; the spectral geometry import stays here. -/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma fourier_tensor_scale (p : Outcome → Q) (a b c : Outcome) :
    centeredTensor QBasis.coordinate.point fourierBasis.point
      (fun j => projector (phasedFourierColumn p j)) a b c =
      ((unscaledFourierColumn b a *
        qInner (unscaledFourierColumn b) (unscaledPhasedFourierColumn p c) *
        star (unscaledPhasedFourierColumn p c a)).re-1)/9 := by
  have ht : fourierScale*(fourierScale*fourierScale*fourierScale)=(1/9:ℝ) := by
    calc
      _=(fourierScale*fourierScale)*(fourierScale*fourierScale) := by ring
      _=1/9 := by rw [fourierScale_square]; norm_num
  change centeredTensor QBasis.coordinate.point
    (fun j => projector (fourierBasis.column j))
    (fun j => projector (phasedFourierColumn p j)) a b c = _
  rw [coordinate_tensor_projectors, fourierBasis_column_scale,
    phasedFourier_column_scale, qInner_smul_both]
  simp only [Pi.smul_apply, star_smul, star_trivial, smul_mul_assoc,
    mul_smul_comm, smul_smul, Quaternion.re_smul, smul_eq_mul]
  rw [ht]
  ring


end QuaternionicMUB
