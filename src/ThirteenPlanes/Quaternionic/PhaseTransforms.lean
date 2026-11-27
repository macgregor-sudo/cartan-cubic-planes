module

public import ThirteenPlanes.Quaternionic.Transforms

@[expose] public section

/-! Native phase changes, with exact overlap and whole-tensor invariance. -/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma diagonal_product_apply (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i)=1)
    (V : QBasis) (i j : Outcome) :
    ((diagonalBasis p hp).product V).mat i j = p i * V.mat i j := by
  rw [QBasis.product_mat]
  change (Matrix.diagonal p * V.mat) i j = _
  rw [Matrix.diagonal_mul]

lemma rightPhases_mat_apply (V : QBasis) (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (i j : Outcome) :
    (V.rightPhases p hp).mat i j = V.mat i j * p j := by
  exact congrFun (V.rightPhases_column p hp j) i

lemma QBasis.rightPhases_mutuallyUnbiased (U V : QBasis) (p q : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (hq : ∀ i, Quaternion.normSq (q i)=1) :
    (U.rightPhases p hp).MutuallyUnbiased (V.rightPhases q hq) ↔ U.MutuallyUnbiased V := by
  simp only [QBasis.MutuallyUnbiased, QBasis.rightPhases_column, qInner_right_mul,
    map_mul, Quaternion.normSq_star, hp, hq, one_mul, mul_one]

lemma basisW_rightPhases (U V W : QBasis) (p q r : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (hq : ∀ i, Quaternion.normSq (q i)=1)
    (hr : ∀ i, Quaternion.normSq (r i)=1) :
    basisW (U.rightPhases p hp) (V.rightPhases q hq) (W.rightPhases r hr) = basisW U V W := by
  simp only [basisW, w, centeredTensor, QBasis.rightPhases_point]

lemma basisS_rightPhases (U V W : QBasis) (p q r : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (hq : ∀ i, Quaternion.normSq (q i)=1)
    (hr : ∀ i, Quaternion.normSq (r i)=1) :
    basisS (U.rightPhases p hp) (V.rightPhases q hq) (W.rightPhases r hr) = basisS U V W := by
  change 6 * basisW _ _ _ = 6 * basisW U V W
  rw [basisW_rightPhases]

lemma coordinate_rightPhases_eq_diagonal (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) :
    QBasis.coordinate.rightPhases p hp = diagonalBasis p hp := by
  apply QBasis.eq_of_mat_eq
  change (QBasis.coordinate.product (diagonalBasis p hp)).mat = _
  rw [QBasis.product_mat]
  change 1 * _ = _
  rw [one_mul]

lemma diagonalBasis_point (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (a : Outcome) :
    (diagonalBasis p hp).point a = QBasis.coordinate.point a := by
  rw [← coordinate_rightPhases_eq_diagonal p hp, QBasis.rightPhases_point]

end QuaternionicMUB
