module

public import ThirteenPlanes.Quaternionic.FourierCoordinates

@[expose] public section

/-!
# Exact polynomial bridges assembled from small native coordinate identities

The finite native entry formulas are quadratic. Their complete sums of squares
are evaluated by the separate first/second Fourier moments. This avoids a large
quartic coordinate expansion while retaining all nine overlaps and 27 entries.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

/-- The sum of all nine squared overlap errors, with no unit-norm premise. -/
theorem fourierOverlapVariance_identity (p : Outcome → Q) :
    fourierOverlapVariance p = ((∑ i, Quaternion.normSq (p i))-3)^2/9 +
      (2/9:ℝ)*phaseCorrelationEnergy p := by
  calc
    fourierOverlapVariance p = ∑ b, ∑ c,
      (((∑ i, Quaternion.normSq (p i))-3)/9 +
        (2/9:ℝ)*mixedFourierRe (Heron.correlation (phaseA p))
          (Heron.correlation (phaseB p)) b c)^2 := by
      unfold fourierOverlapVariance
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [fourier_overlap_entry]
      ring
    _ = _ := by
      rw [mixedFourierRe_affine_sum_sq]
      unfold phaseCorrelationEnergy
      ring

lemma phaseEdgePairs_identity (p : Outcome → Q) :
    (∑ a, (Complex.normSq (phaseEdgesA p (firstIncident a)+phaseEdgesA p (secondIncident a))+
      Complex.normSq (phaseEdgesB p (firstIncident a)+phaseEdgesB p (secondIncident a)))) =
      phasePairEnergy p+phaseCorrelationEnergy p := by
  calc
    _ = (Complex.normSq (phaseEdgesA p 0+phaseEdgesA p 1)+
          Complex.normSq (phaseEdgesA p 0+phaseEdgesA p 2)+
          Complex.normSq (phaseEdgesA p 1+phaseEdgesA p 2)) +
        (Complex.normSq (phaseEdgesB p 0+phaseEdgesB p 1)+
          Complex.normSq (phaseEdgesB p 0+phaseEdgesB p 2)+
          Complex.normSq (phaseEdgesB p 1+phaseEdgesB p 2)) := by
      simp [firstIncident, secondIncident, Fin.sum_univ_succ]
      <;> ring
    _ = (Complex.normSq (phaseEdgesA p 0)+Complex.normSq (phaseEdgesA p 1)+
          Complex.normSq (phaseEdgesA p 2)+
          Complex.normSq (phaseEdgesA p 0+phaseEdgesA p 1+phaseEdgesA p 2)) +
        (Complex.normSq (phaseEdgesB p 0)+Complex.normSq (phaseEdgesB p 1)+
          Complex.normSq (phaseEdgesB p 2)+
          Complex.normSq (phaseEdgesB p 0+phaseEdgesB p 1+phaseEdgesB p 2)) := by
      rw [complex_three_pair_norms, complex_three_pair_norms]
    _ = _ := by
      simp [phaseEdgesA, phaseEdgesB, phasePairEnergy, phaseCorrelationEnergy,
        Heron.correlation, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
      <;> ring

lemma phased_fourier_tensor_row_square (p : Outcome → Q) (a : Outcome) :
    (∑ b, ∑ c, (centeredTensor QBasis.coordinate.point fourierBasis.point
      (fun j => projector (phasedFourierColumn p j)) a b c)^2) =
      (Quaternion.normSq (p a)-1)^2/9 +
        (Complex.normSq (phaseEdgesA p (firstIncident a)+phaseEdgesA p (secondIncident a))+
         Complex.normSq (phaseEdgesB p (firstIncident a)+phaseEdgesB p (secondIncident a)))/18 := by
  calc
    _ = ∑ b, ∑ c, ((Quaternion.normSq (p a)-1)/9+
        (1/9:ℝ)*mixedFourierRe
          (phaseEdgesA p (firstIncident a)+phaseEdgesA p (secondIncident a))
          (phaseEdgesB p (firstIncident a)+phaseEdgesB p (secondIncident a)) b c)^2 := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [phased_fourier_tensor_entry, mixedFourierRe_add]
      ring
    _ = _ := by rw [mixedFourierRe_affine_sum_sq]; ring

/-- The actual complete centered triple weight, including the precise norm and
correlation corrections outside the unbiased unit-phase locus. -/
theorem rawPhasedFourierS_identity (p : Outcome → Q) :
    rawPhasedFourierS p = (2/3:ℝ)*(∑ i, (Quaternion.normSq (p i)-1)^2) +
      phasePairEnergy p/3 + phaseCorrelationEnergy p/3 := by
  calc
    rawPhasedFourierS p = 6*(∑ a,
        ((Quaternion.normSq (p a)-1)^2/9+
          (Complex.normSq (phaseEdgesA p (firstIncident a)+phaseEdgesA p (secondIncident a))+
           Complex.normSq (phaseEdgesB p (firstIncident a)+phaseEdgesB p (secondIncident a)))/18)) := by
      simp only [rawPhasedFourierS, w, phased_fourier_tensor_row_square]
    _ = (2/3:ℝ)*(∑ i, (Quaternion.normSq (p i)-1)^2)+
        (1/3:ℝ)*(∑ a,
          (Complex.normSq (phaseEdgesA p (firstIncident a)+phaseEdgesA p (secondIncident a))+
           Complex.normSq (phaseEdgesB p (firstIncident a)+phaseEdgesB p (secondIncident a)))) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring
    _ = _ := by rw [phaseEdgePairs_identity]; ring

end QuaternionicMUB
