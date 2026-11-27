module

public import ThirteenPlanes.Quaternionic.HadamardNormalForm

@[expose] public section

/-!
# Reduction of an arbitrary native MUB triple without changing its cubic weight

The second application of Hadamard normalization is used only as a factorization
of the third basis. Its left diagonal factors are retained, so the already
fixed coordinate/Fourier pair is not changed.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma QBasis.product_coordinate (U : QBasis) : U.product QBasis.coordinate = U := by
  apply QBasis.eq_of_mat_eq
  rw [QBasis.product_mat]
  exact mul_one _

lemma QBasis.product_mutuallyUnbiased (U V W : QBasis) :
    (U.product V).MutuallyUnbiased (U.product W) ↔ V.MutuallyUnbiased W :=
  U.adjoint.transport_mutuallyUnbiased V W

lemma basisS_product (U V W Z : QBasis) :
    basisS (U.product V) (U.product W) (U.product Z) = basisS V W Z :=
  basisS_transport U.adjoint V W Z

lemma QBasis.mutuallyUnbiased_iff_trace (U V : QBasis) :
    U.MutuallyUnbiased V ↔ ∀ a b, traceForm (U.point a) (V.point b) = (1/3:ℝ) := by
  simp only [QBasis.MutuallyUnbiased, QBasis.point, traceForm_projector_projector]

lemma QBasis.mutuallyUnbiased_congr_points {U U' V V' : QBasis}
    (hU : ∀ a, U.point a=U'.point a) (hV : ∀ a, V.point a=V'.point a) :
    U.MutuallyUnbiased V ↔ U'.MutuallyUnbiased V' := by
  simp only [QBasis.mutuallyUnbiased_iff_trace, hU, hV]

lemma basisS_congr_points {U U' V V' W W' : QBasis}
    (hU : ∀ a, U.point a=U'.point a) (hV : ∀ a, V.point a=V'.point a)
    (hW : ∀ a, W.point a=W'.point a) : basisS U V W=basisS U' V' W' := by
  simp only [basisS, s, w, centeredTensor, hU, hV, hW]

lemma QBasis.transport_product (U V : QBasis) : U.transport (U.product V)=V := by
  apply QBasis.eq_of_mat_eq
  change U.matᴴ*(U.product V).mat=V.mat
  rw [QBasis.product_mat, ← mul_assoc, U.adjoint_mul, one_mul]

lemma QBasis.transport_rightPhases (U V : QBasis) (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) :
    U.transport (V.rightPhases p hp)=(U.transport V).rightPhases p hp := by
  apply QBasis.eq_of_mat_eq
  change U.matᴴ*(V.product (diagonalBasis p hp)).mat=
    ((U.transport V).product (diagonalBasis p hp)).mat
  rw [QBasis.product_mat, QBasis.product_mat]
  change U.matᴴ*(V.mat*(diagonalBasis p hp).mat)=
    (U.matᴴ*V.mat)*(diagonalBasis p hp).mat
  rw [mul_assoc]

def phasedFourierBasis (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) : QBasis :=
  (diagonalBasis p hp).product fourierBasis

lemma diagonal_transport_fourier (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i)=1) :
    (diagonalBasis p hp).transport fourierBasis =
      phasedFourierBasis (fun i => star (p i)) (by intro i; simpa using hp i) := by
  apply QBasis.eq_of_mat_eq
  change (Matrix.diagonal p)ᴴ*fourierBasis.mat=
    ((diagonalBasis (fun i => star (p i)) _).product fourierBasis).mat
  rw [QBasis.product_mat]
  change (Matrix.diagonal p)ᴴ*fourierBasis.mat=
    Matrix.diagonal (fun i => star (p i))*fourierBasis.mat
  rw [Matrix.diagonal_conjTranspose]
  rfl

/-- An arbitrary coordinate-unbiased basis has exactly the point frame of a
left-diagonal Fourier basis; right phases have no effect on the points. -/
theorem exists_phasedFourier_points (V : QBasis)
    (hV : QBasis.coordinate.MutuallyUnbiased V) :
    ∃ p : Outcome → Q, ∃ hp : ∀ i, Quaternion.normSq (p i)=1,
      ∀ a, V.point a=(phasedFourierBasis p hp).point a := by
  obtain ⟨p, q, hp, hq, h⟩ := hadamard_normal_form V hV
  refine ⟨fun i => star (p i), (by intro i; simpa using hp i), ?_⟩
  intro a
  have hh := congrArg (fun X : QBasis => ((diagonalBasis p hp).transport X).point a) h
  rw [QBasis.transport_rightPhases, QBasis.transport_product,
    QBasis.rightPhases_point, diagonal_transport_fourier] at hh
  exact hh

/-- The unrestricted native triple reduction preserves the actual complete
27-entry cubic weight, and carries the ordinary overlap hypotheses forward. -/
theorem mub_triple_reduction (U V W : QBasis)
    (hUV : U.MutuallyUnbiased V) (hUW : U.MutuallyUnbiased W)
    (hVW : V.MutuallyUnbiased W) :
    ∃ p : Outcome → Q, ∃ hp : ∀ i, Quaternion.normSq (p i)=1,
      QBasis.coordinate.MutuallyUnbiased (phasedFourierBasis p hp) ∧
      fourierBasis.MutuallyUnbiased (phasedFourierBasis p hp) ∧
      basisS U V W = basisS QBasis.coordinate fourierBasis (phasedFourierBasis p hp) := by
  let V0 := U.transport V
  let W0 := U.transport W
  have hV0 : QBasis.coordinate.MutuallyUnbiased V0 := by
    simpa only [QBasis.transport_self] using (U.transport_mutuallyUnbiased U V).mpr hUV
  have hW0 : QBasis.coordinate.MutuallyUnbiased W0 := by
    simpa only [QBasis.transport_self] using (U.transport_mutuallyUnbiased U W).mpr hUW
  have hVW0 : V0.MutuallyUnbiased W0 := (U.transport_mutuallyUnbiased V W).mpr hVW
  obtain ⟨p, q, hp, hq, hn⟩ := hadamard_normal_form V0 hV0
  let L := diagonalBasis p hp
  let C1 := L.product QBasis.coordinate
  let V1 := L.product V0
  let W1 := L.product W0
  have hC : ∀ a, C1.point a=QBasis.coordinate.point a := by
    intro a
    rw [show C1=L by exact L.product_coordinate]
    exact diagonalBasis_point p hp a
  have hF : ∀ a, V1.point a=fourierBasis.point a := by
    intro a
    calc
      V1.point a=(V1.rightPhases q hq).point a := (V1.rightPhases_point q hq a).symm
      _=fourierBasis.point a := congrArg (fun X : QBasis => X.point a) hn
  have hC1W1 : C1.MutuallyUnbiased W1 :=
    (L.product_mutuallyUnbiased QBasis.coordinate W0).mpr hW0
  have hV1W1 : V1.MutuallyUnbiased W1 := (L.product_mutuallyUnbiased V0 W0).mpr hVW0
  have hcoordW1 : QBasis.coordinate.MutuallyUnbiased W1 :=
    (QBasis.mutuallyUnbiased_congr_points hC (fun _ => rfl)).mp hC1W1
  have hfourierW1 : fourierBasis.MutuallyUnbiased W1 :=
    (QBasis.mutuallyUnbiased_congr_points hF (fun _ => rfl)).mp hV1W1
  obtain ⟨r, hr, hW⟩ := exists_phasedFourier_points W1 hcoordW1
  refine ⟨r, hr,
    (QBasis.mutuallyUnbiased_congr_points (fun _ => rfl) hW).mp hcoordW1,
    (QBasis.mutuallyUnbiased_congr_points (fun _ => rfl) hW).mp hfourierW1, ?_⟩
  have hfirst : basisS QBasis.coordinate V0 W0=basisS U V W := by
    simpa only [QBasis.transport_self] using basisS_transport U U V W
  calc
    basisS U V W=basisS QBasis.coordinate V0 W0 := hfirst.symm
    _=basisS C1 V1 W1 := (basisS_product L QBasis.coordinate V0 W0).symm
    _=basisS QBasis.coordinate fourierBasis (phasedFourierBasis r hr) :=
      basisS_congr_points hC hF hW

end QuaternionicMUB
