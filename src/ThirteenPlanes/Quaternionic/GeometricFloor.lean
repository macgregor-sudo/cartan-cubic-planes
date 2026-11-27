module

public import ThirteenPlanes.Quaternionic.NativeFloor
public import ThirteenPlanes.Quaternionic.NativeFrameShare

@[expose] public section

/-! The full quaternionic floor for the literal half-projection-trace share. -/

open scoped BigOperators

namespace QuaternionicMUB

/-- The Fourier matrix used in the native normal form is the displayed matrix. -/
theorem fourierBasis_entry (i j : Outcome) :
    fourierBasis.mat i j = (1 / Real.sqrt 3) • omega ^ (i.val * j.val) := by
  have h₂ : omega ^ 2 = star omega := by rw [pow_two, omega_square]
  have h₃ : omega ^ 3 = 1 := by simpa only [pow_succ, pow_zero, one_mul] using omega_cube
  have h₄ : omega ^ 4 = omega := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_succ, h₃, one_mul]
  change fourierMatrix i j = _
  rw [← fourierScale_eq_inv_sqrt, fourierMatrix, Matrix.smul_apply]
  congr 1
  fin_cases i <;> fin_cases j <;> norm_num [h₂, h₄]

/-- The two complex coefficients of a quaternion use the paper's fixed i,j convention. -/
theorem phaseA_phaseB_quaternion (p : Outcome → Q) (i : Outcome) :
    p i = quaternionOfComplexPair (phaseA p i) 0 +
      quaternionOfComplexPair (phaseB p i) 0 * qj := by
  apply Quaternion.ext <;> simp [phaseA, phaseB, quaternionOfComplexPair, qj]

/-- Both directions of the actual-basis normalization in quaternionic Fourier normal form. -/
theorem quaternionicNormalForm :
    (∀ U V W : QBasis, IsUnbiasedTriple U V W →
      ∃ (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i) = 1),
        IsFourierNormalForm U V W p hp) ∧
    (∀ (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i) = 1),
      IsUnbiasedTriple QBasis.coordinate fourierBasis (phasedFourierBasis p hp) ↔
        Heron.correlation (phaseA p) = 0 ∧ Heron.correlation (phaseB p) = 0) :=
  ⟨exists_fourierNormalForm, fourierNormalTriple_iff_correlations⟩

/-- The two exact geometric share formulas in quaternionic trace-share identity. -/
theorem quaternionicNormalFormShare (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i) = 1)
    (ha : Heron.correlation (phaseA p) = 0) (hb : Heron.correlation (phaseB p) = 0) :
    let X := fun i => Complex.normSq (phaseA p i)
    let Y := fun i => Complex.normSq (phaseB p i)
    let s := basisGeometricShare QBasis.coordinate fourierBasis (phasedFourierBasis p hp)
    s = (1 / 3 : ℝ) * (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      (X i * X j + Y i * Y j)) ∧
    s = (3 + (phaseZ p 0 * phaseZ p 1 + phaseZ p 1 * phaseZ p 2 +
      phaseZ p 2 * phaseZ p 0)) / 6 := by
  dsimp only
  have hu := (fourierNormalTriple_iff_correlations p hp).mpr ⟨ha, hb⟩
  have h₂ :
      basisGeometricShare QBasis.coordinate fourierBasis (phasedFourierBasis p hp) =
        (3 + (phaseZ p 0 * phaseZ p 1 + phaseZ p 1 * phaseZ p 2 +
          phaseZ p 2 * phaseZ p 0)) / 6 :=
    (basisGeometricShare_eq_basisS _ _ _ hu.1 hu.2.1 hu.2.2).trans
      (basisS_phased_formula p hp ha hb)
  refine ⟨?_, h₂⟩
  have hs : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        (Complex.normSq (phaseA p i) * Complex.normSq (phaseA p j) +
          Complex.normSq (phaseB p i) * Complex.normSq (phaseB p j))) = phasePairEnergy p := by
    norm_num [Finset.sum_filter, Fin.sum_univ_three, phasePairEnergy]
    ring
  rw [hs, phasePairEnergy_unit p hp]
  linarith only [h₂]

/-- All assertions of the sharp quaternionic triple-share bound for the actual half-trace share of three native
quaternionic bases. The attainment basis uses `attainmentPhases_paper_formula`. -/
theorem quaternionicFloor :
    (∀ U V W : QBasis, IsUnbiasedTriple U V W →
      1 - 1 / Real.sqrt 3 ≤ basisGeometricShare U V W) ∧
    (IsUnbiasedTriple QBasis.coordinate fourierBasis attainingBasis ∧
      attainingBasis = phasedFourierBasis attainmentPhases attainmentPhases_unit ∧
      basisGeometricShare QBasis.coordinate fourierBasis attainingBasis = 1 - 1 / Real.sqrt 3) ∧
    (∀ (U V W : QBasis), IsUnbiasedTriple U V W →
      ∀ (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i) = 1),
      IsFourierNormalForm U V W p hp →
      (basisGeometricShare U V W = 1 - 1 / Real.sqrt 3 ↔
        Heron.FloorBalanceShape (phaseZ p 0) (phaseZ p 1) (phaseZ p 2))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V W h
    rw [basisGeometricShare_eq_basisS U V W h.1 h.2.1 h.2.2]
    exact nativeTripleFloor.1 U V W h
  · have h := nativeTripleFloor.2.1.1
    refine ⟨h, rfl, ?_⟩
    rw [basisGeometricShare_eq_basisS QBasis.coordinate fourierBasis attainingBasis h.1 h.2.1 h.2.2]
    exact nativeTripleFloor.2.1.2
  · intro U V W h p hp hn
    rw [basisGeometricShare_eq_basisS U V W h.1 h.2.1 h.2.2]
    exact nativeTripleFloor.2.2 U V W h p hp hn

end QuaternionicMUB
