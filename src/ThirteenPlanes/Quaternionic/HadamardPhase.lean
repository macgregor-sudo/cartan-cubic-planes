module

public import ThirteenPlanes.Quaternionic.Fourier
public import ThirteenPlanes.Quaternionic.ImaginaryConjugation

@[expose] public section

/-!
# The nonreal phase of a dephased quaternionic Hadamard matrix

The two unit-norm equations force real part -1/2. The preceding explicit
unit-imaginary conjugator then sends this arbitrary phase to the specified
complex cube root. No classification theorem is assumed.
-/

noncomputable section
namespace QuaternionicMUB

lemma hadamard_phase_real_part (a : Q) (ha : Quaternion.normSq a = 1)
    (hb : Quaternion.normSq (-1-a) = 1) : a.re = -1/2 := by
  norm_num [Quaternion.normSq_def'] at ha hb
  nlinarith

/-- The phase and its conjugate in every dephased order-three Hadamard block
can be normalized simultaneously by a literal unit quaternion. -/
theorem hadamard_phase_conjugator (a : Q) (ha : Quaternion.normSq a = 1)
    (hb : Quaternion.normSq (-1-a) = 1) :
    ∃ g : Q, Quaternion.normSq g = 1 ∧ g*a*star g = omega := by
  have hre := hadamard_phase_real_part a ha hb
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  let u : Q := (2*Real.sqrt 3/3) • (a + (1/2:ℝ) • (1:Q))
  have hure : u.re = 0 := by simp [u, hre] <;> ring
  have hsmall : Quaternion.normSq (a + (1/2:ℝ) • (1:Q)) = 3/4 := by
    norm_num [Quaternion.normSq_def', hre] at ha ⊢
    nlinarith
  have hun : Quaternion.normSq u = 1 := by
    dsimp [u]
    rw [Quaternion.normSq_smul, hsmall]
    nlinarith
  obtain ⟨g, hgn, hgu⟩ := exists_unit_conjugator_to_i u hure hun
  have hfactor : (Real.sqrt 3/2)*(2*Real.sqrt 3/3)=1 := by nlinarith
  have hadecomp : a = (-1/2:ℝ) • (1:Q) + (Real.sqrt 3/2) • u := by
    dsimp [u]
    rw [smul_smul, hfactor, one_smul]
    rw [show (-1/2:ℝ) = -(1/2:ℝ) by norm_num, neg_smul]
    abel
  have homega : (-1/2:ℝ) • (1:Q) + (Real.sqrt 3/2) • qi = omega := by
    ext <;> simp [qi, omega]
  refine ⟨g, hgn, ?_⟩
  calc
    g*a*star g = (-1/2:ℝ) • (g*star g) +
        (Real.sqrt 3/2) • (g*u*star g) := by
      rw [hadecomp]
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
    _ = (-1/2:ℝ) • (1:Q) + (Real.sqrt 3/2) • qi := by
      rw [hgu, Quaternion.self_mul_star, hgn, Quaternion.coe_one]
    _ = omega := homega

end QuaternionicMUB
