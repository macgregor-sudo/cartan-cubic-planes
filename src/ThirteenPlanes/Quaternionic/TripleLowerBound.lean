module

public import ThirteenPlanes.Quaternionic.BasisReduction
public import ThirteenPlanes.Quaternionic.FourierPolynomials

@[expose] public section

/-!
# The native sharp lower inequality for arbitrary quaternionic MUB triples

All hypotheses below are ordinary basis overlap equations. The two complex
correlations and the scalar Heron inequality are derived only after the native
weight-preserving reduction, and the bound is on the full original cubic tensor.
Attainment is a separate explicit construction.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma phasedFourierBasis_column (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (c : Outcome) :
    (phasedFourierBasis p hp).column c=phasedFourierColumn p c := by
  funext i
  exact diagonal_product_apply p hp fourierBasis i c

lemma basisS_phased_eq_raw (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) :
    basisS QBasis.coordinate fourierBasis (phasedFourierBasis p hp)=rawPhasedFourierS p := by
  simp only [basisS, s, rawPhasedFourierS, w, centeredTensor, QBasis.point,
    phasedFourierBasis_column]

lemma fourier_unbiased_correlations (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1)
    (h : fourierBasis.MutuallyUnbiased (phasedFourierBasis p hp)) :
    Heron.correlation (phaseA p)=0 ∧ Heron.correlation (phaseB p)=0 := by
  have he : fourierOverlapVariance p=0 := by
    unfold fourierOverlapVariance
    have hh : ∀ b c, Quaternion.normSq
        (qInner (fourierBasis.column b) (phasedFourierColumn p c))=(1/3:ℝ) := by
      intro b c
      simpa only [phasedFourierBasis_column] using h b c
    simp only [hh, sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
  rw [fourierOverlapVariance_identity] at he
  have ha := Complex.normSq_nonneg (Heron.correlation (phaseA p))
  have hb := Complex.normSq_nonneg (Heron.correlation (phaseB p))
  have hs := sq_nonneg ((∑ i, Quaternion.normSq (p i))-3)
  dsimp only [phaseCorrelationEnergy] at he
  constructor
  · apply Complex.normSq_eq_zero.mp
    nlinarith
  · apply Complex.normSq_eq_zero.mp
    nlinarith

lemma fourier_unbiased_of_correlations (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1)
    (ha : Heron.correlation (phaseA p)=0) (hb : Heron.correlation (phaseB p)=0) :
    fourierBasis.MutuallyUnbiased (phasedFourierBasis p hp) := by
  have he : fourierOverlapVariance p=0 := by
    rw [fourierOverlapVariance_identity]
    simp [hp, phaseCorrelationEnergy, ha, hb]
  unfold fourierOverlapVariance at he
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun b _ => Finset.sum_nonneg fun c _ => sq_nonneg _)).mp he
  intro b c
  rw [phasedFourierBasis_column]
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg
    (fun c _ => sq_nonneg _)).mp (hh b (Finset.mem_univ b))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hrow c (Finset.mem_univ c)))

def phaseZ (p : Outcome → Q) (i : Outcome) : ℝ :=
  Complex.normSq (phaseA p i)-Complex.normSq (phaseB p i)

lemma phasePairEnergy_unit (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) :
    phasePairEnergy p=(3+(phaseZ p 0*phaseZ p 1+phaseZ p 1*phaseZ p 2+
      phaseZ p 2*phaseZ p 0))/2 := by
  have hb : ∀ i, Complex.normSq (phaseB p i)=1-Complex.normSq (phaseA p i) := by
    intro i
    have h := phase_normSq_split p i
    rw [hp] at h
    linarith
  simp only [phasePairEnergy, phaseZ, hb]
  ring

/-- The source scalar expression equals the actual native 27-entry weight. -/
lemma basisS_phased_formula (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1)
    (ha : Heron.correlation (phaseA p)=0) (hb : Heron.correlation (phaseB p)=0) :
    basisS QBasis.coordinate fourierBasis (phasedFourierBasis p hp)=
      (3+(phaseZ p 0*phaseZ p 1+phaseZ p 1*phaseZ p 2+phaseZ p 2*phaseZ p 0))/6 := by
  rw [basisS_phased_eq_raw, rawPhasedFourierS_identity, phasePairEnergy_unit p hp]
  simp [hp, phaseCorrelationEnergy, ha, hb]
  <;> ring

/-- Native lower bound for every three mutually unbiased quaternionic bases. -/
theorem triple_lower_bound (U V W : QBasis)
    (hUV : U.MutuallyUnbiased V) (hUW : U.MutuallyUnbiased W)
    (hVW : V.MutuallyUnbiased W) :
    1-1/Real.sqrt 3 ≤ basisS U V W := by
  obtain ⟨p, hp, _, hf, hweight⟩ := mub_triple_reduction U V W hUV hUW hVW
  obtain ⟨ha, hb⟩ := fourier_unbiased_correlations p hp hf
  have hu : ∀ i, Complex.normSq (phaseA p i)+Complex.normSq (phaseB p i)=1 := by
    intro i
    rw [phase_normSq_split, hp]
  have hscalar := Heron.lower_bound_of_autocorrelations (phaseA p) (phaseB p) hu ha hb
  rw [hweight, basisS_phased_formula p hp ha hb]
  exact hscalar

/-- The identical lower inequality in the unrescaled source tensor norm. -/
theorem triple_weight_lower_bound (U V W : QBasis)
    (hUV : U.MutuallyUnbiased V) (hUW : U.MutuallyUnbiased W)
    (hVW : V.MutuallyUnbiased W) :
    (3-Real.sqrt 3)/18 ≤ basisW U V W := by
  have h := triple_lower_bound U V W hUV hUW hVW
  change 1-1/Real.sqrt 3 ≤ 6*basisW U V W at h
  have hi : 1/Real.sqrt 3=Real.sqrt 3/3 := fourierScale_eq_inv_sqrt.symm
  rw [hi] at h
  linarith

end QuaternionicMUB
