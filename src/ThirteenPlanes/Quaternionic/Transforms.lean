module

public import ThirteenPlanes.Quaternionic.Quartic

@[expose] public section

/-!
# Native changes of quaternionic basis and phase invariance

Every operation below acts on the literal two-sided unitary matrix carrier.
Common left unitary changes preserve all overlaps and the full centered cubic
tensor. Right column phases preserve each actual rank-one projector.
-/

noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma QBasis.eq_of_mat_eq {U V : QBasis} (h : U.mat = V.mat) : U=V := by
  cases U
  cases V
  cases h
  rfl

/-- Apply the inverse of the same native unitary to all columns. -/
def QBasis.transport (U V : QBasis) : QBasis where
  mat := U.matᴴ * V.mat
  adjoint_mul := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
    rw [← mul_assoc U.mat U.matᴴ V.mat, U.mul_adjoint, one_mul, V.adjoint_mul]
  mul_adjoint := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
    rw [← mul_assoc V.mat V.matᴴ U.mat, V.mul_adjoint, one_mul, U.adjoint_mul]

def QBasis.adjoint (U : QBasis) : QBasis where
  mat := U.matᴴ
  adjoint_mul := by simpa only [Matrix.conjTranspose_conjTranspose] using U.mul_adjoint
  mul_adjoint := by simpa only [Matrix.conjTranspose_conjTranspose] using U.adjoint_mul

def QBasis.product (U V : QBasis) : QBasis := U.adjoint.transport V

@[simp] lemma QBasis.product_mat (U V : QBasis) : (U.product V).mat = U.mat * V.mat := by
  simp [QBasis.product, QBasis.adjoint, QBasis.transport]

@[simp] lemma QBasis.transport_self (U : QBasis) : U.transport U = QBasis.coordinate := by
  apply QBasis.eq_of_mat_eq
  exact U.adjoint_mul

lemma QBasis.transport_column (U V : QBasis) (a : Outcome) :
    (U.transport V).column a = matrixAction U.matᴴ (V.column a) := rfl

lemma qInner_unitary_transport (U : QBasis) (u v : QVec) :
    qInner (matrixAction U.matᴴ u) (matrixAction U.matᴴ v) = qInner u v := by
  rw [qInner_matrixAction_adjoint, Matrix.conjTranspose_conjTranspose]
  have h : matrixAction U.mat (matrixAction U.matᴴ v) = v := by
    change ((matrixAction U.mat).comp (matrixAction U.matᴴ)) v = v
    rw [← matrixAction_mul, U.mul_adjoint, matrixAction_one]
    rfl
  rw [h]

lemma QBasis.transport_mutuallyUnbiased (U V W : QBasis) :
    (U.transport V).MutuallyUnbiased (U.transport W) ↔ V.MutuallyUnbiased W := by
  simp only [QBasis.MutuallyUnbiased, QBasis.transport_column, qInner_unitary_transport]

lemma projector_matrixAction (A : QMat) (u : QVec) :
    projector (matrixAction A u) = A * projector u * Aᴴ := by
  change Matrix.vecMulVec (A *ᵥ u) (star (A *ᵥ u)) =
    A * Matrix.vecMulVec u (star u) * Aᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma QBasis.transport_point (U V : QBasis) (a : Outcome) :
    (U.transport V).point a = unitaryConjugate U (V.point a) := by
  rw [QBasis.point, QBasis.transport_column, projector_matrixAction]
  simp only [Matrix.conjTranspose_conjTranspose, QBasis.point, unitaryConjugate]

lemma unitaryConjugate_add (U : QBasis) (A B : QMat) :
    unitaryConjugate U (A+B) = unitaryConjugate U A + unitaryConjugate U B := by
  simp only [unitaryConjugate, mul_add, add_mul]

lemma unitaryConjugate_smul (U : QBasis) (r : ℝ) (A : QMat) :
    unitaryConjugate U (r • A) = r • unitaryConjugate U A := by
  simp only [unitaryConjugate, mul_smul_comm, smul_mul_assoc]

lemma unitaryConjugate_jordan (U : QBasis) (A B : QMat) :
    unitaryConjugate U (jordan A B) =
      jordan (unitaryConjugate U A) (unitaryConjugate U B) := by
  simp only [jordan, unitaryConjugate_smul, unitaryConjugate_add, unitaryConjugate_mul]

lemma traceForm_unitaryConjugate (U : QBasis) (A B : QMat) :
    traceForm (unitaryConjugate U A) (unitaryConjugate U B) = traceForm A B := by
  simp only [traceForm_eq_rtrace_mul, ← unitaryConjugate_mul, rtrace_unitaryConjugate]

lemma centeredTensor_unitaryConjugate (U : QBasis) (F G H : Outcome → QMat)
    (a b c : Outcome) :
    centeredTensor (fun i => unitaryConjugate U (F i))
      (fun i => unitaryConjugate U (G i)) (fun i => unitaryConjugate U (H i)) a b c =
      centeredTensor F G H a b c := by
  simp only [centeredTensor, ← unitaryConjugate_jordan, traceForm_unitaryConjugate]

/-- The whole native triple weight is invariant, entry by entry. -/
theorem basisW_transport (U V W Z : QBasis) :
    basisW (U.transport V) (U.transport W) (U.transport Z) = basisW V W Z := by
  simp only [basisW, w, centeredTensor, QBasis.transport_point,
    ← unitaryConjugate_jordan, traceForm_unitaryConjugate]

theorem basisS_transport (U V W Z : QBasis) :
    basisS (U.transport V) (U.transport W) (U.transport Z) = basisS V W Z := by
  change 6*basisW (U.transport V) (U.transport W) (U.transport Z) = 6*basisW V W Z
  rw [basisW_transport]

/-- A literal diagonal unitary from arbitrary unit quaternion phases. -/
def diagonalBasis (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i)=1) : QBasis where
  mat := Matrix.diagonal p
  adjoint_mul := by
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Pi.star_apply,
      Quaternion.star_mul_self, hp, Quaternion.coe_one, Matrix.diagonal_one]
  mul_adjoint := by
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Pi.star_apply,
      Quaternion.self_mul_star, hp, Quaternion.coe_one, Matrix.diagonal_one]

lemma projector_right_phase (u : QVec) (p : Q) (hp : Quaternion.normSq p=1) :
    projector (fun i => u i*p) = projector u := by
  have h : p*star p=1 := by rw [Quaternion.self_mul_star, hp]; rfl
  apply Matrix.ext
  intro i j
  simp only [projector, star_mul]
  calc
    (u i*p)*(star p*star (u j)) = u i*(p*star p)*star (u j) := by simp only [mul_assoc]
    _ = u i*star (u j) := by rw [h]; simp

/-- Independent right column phases act on bases but fix their point frames. -/
def QBasis.rightPhases (V : QBasis) (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) : QBasis := V.product (diagonalBasis p hp)

lemma QBasis.rightPhases_column (V : QBasis) (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (a : Outcome) :
    (V.rightPhases p hp).column a = fun i => V.column a i*p a := by
  funext i
  change (V.product (diagonalBasis p hp)).mat i a = _
  rw [QBasis.product_mat]
  change (V.mat * Matrix.diagonal p) i a = _
  rw [Matrix.mul_diagonal]
  rfl

lemma QBasis.rightPhases_point (V : QBasis) (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) (a : Outcome) :
    (V.rightPhases p hp).point a = V.point a := by
  rw [QBasis.point, QBasis.rightPhases_column, projector_right_phase _ _ (hp a)]
  rfl

end QuaternionicMUB
