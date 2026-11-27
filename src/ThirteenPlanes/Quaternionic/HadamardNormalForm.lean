module

public import ThirteenPlanes.Quaternionic.Dephasing

@[expose] public section

/-!
# Unrestricted quaternionic Hadamard normalization in dimension three

Every native coordinate-unbiased basis is sent to the literal Fourier matrix
by explicit left diagonal unit quaternions and independent right column phases.
The common quaternion conjugation is absorbed into those actual phases.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

/-- No dephased, spectral, orbit, or normal-form premise is required. -/
theorem hadamard_normal_form (V : QBasis)
    (hV : QBasis.coordinate.MutuallyUnbiased V) :
    ∃ p q : Outcome → Q, ∃ hp : ∀ i, Quaternion.normSq (p i)=1,
      ∃ hq : ∀ i, Quaternion.normSq (q i)=1,
      ((diagonalBasis p hp).product V).rightPhases q hq = fourierBasis := by
  obtain ⟨p, q, hp, hq, hr, hc, hn⟩ := exists_dephased_basis V hV
  let K := ((diagonalBasis p hp).product V).rightPhases q hq
  obtain ⟨a, ha, hb, hK⟩ := dephased_hadamard_shape K hr hc hn
  obtain ⟨g, hgn, hga⟩ := hadamard_phase_conjugator a ha hb
  have hgs : g*star g=1 := by rw [Quaternion.self_mul_star, hgn, Quaternion.coe_one]
  have hgminus : g*(-1-a)*star g = star omega := by
    have h : g*(-1-a)*star g = -(1+omega) := by
      rw [show (-1-a:Q) = -(1+a) by abel, mul_neg, neg_mul, mul_add,
        add_mul, mul_one, hgs, hga]
    rw [h]
    exact (eq_neg_of_add_eq_zero_right omega_sum).symm
  have hconj : ∀ i j, g*K.mat i j*star g = fourierMatrix i j := by
    intro i j
    rw [hK]
    fin_cases i <;> fin_cases j <;>
      simp [fourierMatrix, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc,
        hgs, hga, hgminus]
  let p' : Outcome → Q := fun i => g*p i
  let q' : Outcome → Q := fun j => q j*star g
  have hp' : ∀ i, Quaternion.normSq (p' i)=1 := by
    intro i
    simp only [p', map_mul, hgn, hp, mul_one]
  have hq' : ∀ j, Quaternion.normSq (q' j)=1 := by
    intro j
    simp only [q', map_mul, Quaternion.normSq_star, hgn, hq, mul_one]
  refine ⟨p', q', hp', hq', ?_⟩
  apply QBasis.eq_of_mat_eq
  apply Matrix.ext
  intro i j
  rw [rightPhases_mat_apply, diagonal_product_apply]
  change (g*p i)*V.mat i j*(q j*star g) = fourierMatrix i j
  calc
    (g*p i)*V.mat i j*(q j*star g) = g*(p i*V.mat i j*q j)*star g := by
      simp only [mul_assoc]
    _ = g*K.mat i j*star g := by
      dsimp only [K]
      rw [rightPhases_mat_apply, diagonal_product_apply]
    _ = fourierMatrix i j := hconj i j

end QuaternionicMUB
