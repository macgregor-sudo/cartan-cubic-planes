module

public import ThirteenPlanes.Quaternionic.PhaseTransforms
public import ThirteenPlanes.Quaternionic.DephasedHadamard

@[expose] public section

/-!
# Dephasing every coordinate-unbiased quaternionic basis

The two diagonal phase witnesses are constructed from actual matrix entries.
The resulting native unitary has constant positive first row and column and
retains all nine equal entry norms. No Hadamard normal form is assumed.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma sqrt_three_normSq_phase (v : Q) (hv : Quaternion.normSq v = (1/3:ℝ)) :
    Quaternion.normSq (Real.sqrt 3 • star v) = 1 := by
  rw [Quaternion.normSq_smul, Quaternion.normSq_star,
    Real.sq_sqrt (by norm_num), hv]
  norm_num

lemma sqrt_three_star_mul (v : Q) (hv : Quaternion.normSq v = (1/3:ℝ)) :
    (Real.sqrt 3 • star v)*v = fourierScale • (1:Q) := by
  rw [smul_mul_assoc, Quaternion.star_mul_self, hv]
  change Real.sqrt 3 • ((1/3:ℝ):Q) = fourierScale • ((1:ℝ):Q)
  rw [Quaternion.smul_coe, Quaternion.smul_coe]
  congr 1
  dsimp [fourierScale]
  ring

lemma sqrt_three_mul_star (v : Q) (hv : Quaternion.normSq v = (1/3:ℝ)) :
    v*(Real.sqrt 3 • star v) = fourierScale • (1:Q) := by
  rw [mul_smul_comm, Quaternion.self_mul_star, hv]
  change Real.sqrt 3 • ((1/3:ℝ):Q) = fourierScale • ((1:ℝ):Q)
  rw [Quaternion.smul_coe, Quaternion.smul_coe]
  congr 1
  dsimp [fourierScale]
  ring

/-- Every native coordinate-unbiased basis admits actual unit left and right
phases making its first row and column positive constants. -/
theorem exists_dephased_basis (V : QBasis)
    (hV : QBasis.coordinate.MutuallyUnbiased V) :
    ∃ p q : Outcome → Q, ∃ hp : ∀ i, Quaternion.normSq (p i)=1,
      ∃ hq : ∀ i, Quaternion.normSq (q i)=1,
      let K := ((diagonalBasis p hp).product V).rightPhases q hq
      (∀ j, K.mat 0 j = fourierScale • (1:Q)) ∧
      (∀ i, K.mat i 0 = fourierScale • (1:Q)) ∧
      (∀ i j, Quaternion.normSq (K.mat i j) = (1/3:ℝ)) := by
  have hv : ∀ i j, Quaternion.normSq (V.mat i j) = (1/3:ℝ) := by
    intro i j
    simpa only [coordinate_column_inner] using hV i j
  let p : Outcome → Q := fun i => Real.sqrt 3 • star (V.mat i 0)
  have hp : ∀ i, Quaternion.normSq (p i)=1 := fun i => sqrt_three_normSq_phase _ (hv i 0)
  let M : QBasis := (diagonalBasis p hp).product V
  have hm : ∀ i j, Quaternion.normSq (M.mat i j) = (1/3:ℝ) := by
    intro i j
    change Quaternion.normSq (((diagonalBasis p hp).product V).mat i j) = _
    rw [diagonal_product_apply, map_mul, hp, hv, one_mul]
  have hmc : ∀ i, M.mat i 0 = fourierScale • (1:Q) := by
    intro i
    change ((diagonalBasis p hp).product V).mat i 0 = _
    rw [diagonal_product_apply]
    exact sqrt_three_star_mul _ (hv i 0)
  let q : Outcome → Q := fun j => Real.sqrt 3 • star (M.mat 0 j)
  have hq : ∀ i, Quaternion.normSq (q i)=1 := fun i => sqrt_three_normSq_phase _ (hm 0 i)
  have hq0 : q 0 = 1 := by
    dsimp [q]
    rw [hmc]
    simp only [star_smul, star_trivial, star_one, smul_smul,
      sqrt_three_mul_fourierScale, one_smul]
  refine ⟨p, q, hp, hq, ?_, ?_, ?_⟩
  · intro j
    rw [rightPhases_mat_apply]
    exact sqrt_three_mul_star _ (hm 0 j)
  · intro i
    rw [rightPhases_mat_apply, hq0, mul_one]
    exact hmc i
  · intro i j
    rw [rightPhases_mat_apply, map_mul, hq, mul_one]
    exact hm i j

end QuaternionicMUB
