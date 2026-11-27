module

public import ThirteenPlanes.MatrixLineEmbedding
public import ThirteenPlanes.MatrixLineBases
public import ThirteenPlanes.FourPlanesDecomposition

@[expose] public section

set_option backward.privateInPublic true

open scoped Matrix BigOperators ComplexOrder
open AlbertSequential AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes

noncomputable section

/-- The Weyl labels of the computational and the three quadratic Fourier bases. -/
def matrixLineLabel (k : Fin 4) : WeylLabel :=
  Fin.cases (0, 1) (fun a => (1, 2 * qutritResidue a)) k

private theorem matrixLineGrade_valid : ∀ k : Fin 4,
    chargeFrom (matrixLineLabel k) 0 ≠ 0 ∧
      isChargeRepresentative (chargeFrom (matrixLineLabel k) 0) := by decide

/-- The order of these grades follows the published four qutrit bases. -/
def matrixLineGrade (k : Fin 4) : SignedPlaneIndex :=
  ⟨⟨chargeFrom (matrixLineLabel k) 0, (matrixLineGrade_valid k).1⟩,
    (matrixLineGrade_valid k).2⟩

@[simp] theorem matrixLineGrade_third (k : Fin 4) : (matrixLineGrade k).val.val 2 = 0 := rfl

theorem matrixLineGrade_injective : Function.Injective matrixLineGrade := by decide

theorem matrixLineGrade_covers : ∀ p : SignedPlaneIndex, p.val.val 2 = 0 →
    ∃ k : Fin 4, matrixLineGrade k = p := by decide

def matrixLineEigenvalue (k : Fin 4) (b : Fin 3) : ℂ :=
  Fin.cases (chargePhase (qutritResidue b)) (fun _ => chargePhase (-qutritResidue b)) k

private def matrixLineWeyl (k : Fin 4) : ThirteenPlanes.ComplexMatrix3 :=
  weylMatrix (matrixLineLabel k)

private theorem matrixLineWeyl_eigen (k : Fin 4) (b : Fin 3) :
    (matrixLineWeyl k).mulVec (qutritBasisVector k b) =
      matrixLineEigenvalue k b • qutritBasisVector k b := by
  refine Fin.cases ?_ (fun a => ?_) k
  · funext i
    change (weylMatrix (0,1)).mulVec
      (fun j : ZMod 3 => qutritStandardVector b (qutritIndex j)) (qutritResidue i) =
      chargePhase (qutritResidue b) * qutritStandardVector b i
    rw [weylMatrix_mulVec]
    simp only [neg_zero, zero_mul, sub_zero, one_mul, zero_add]
    change chargePhase (qutritResidue i) * qutritStandardVector b i = _
    by_cases h : i = b
    · rw [h]
    · simp [qutritStandardVector, h]
  · exact fourierVector_weylEigen a b

private theorem matrixLineWeyl_projection (k : Fin 4) (b : Fin 3) :
    matrixLineWeyl k * qutritMUBProjection k b =
      matrixLineEigenvalue k b • qutritMUBProjection k b := by
  ext i j
  change (∑ m, matrixLineWeyl k i m *
      (qutritBasisVector k b m * star (qutritBasisVector k b j))) =
    matrixLineEigenvalue k b * (qutritBasisVector k b i * star (qutritBasisVector k b j))
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have h := congrFun (matrixLineWeyl_eigen k b) i
  change (∑ m, matrixLineWeyl k i m * qutritBasisVector k b m) =
    matrixLineEigenvalue k b * qutritBasisVector k b i at h
  rw [h]

private theorem matrixLineWeyl_spectral (k : Fin 4) :
    matrixLineWeyl k = ∑ b, matrixLineEigenvalue k b • qutritMUBProjection k b := by
  calc
    _ = matrixLineWeyl k * ∑ b, qutritMUBProjection k b := by rw [qutritMUBProjection_sum, mul_one]
    _ = _ := by simp only [Finset.mul_sum, matrixLineWeyl_projection]

private theorem matrixLineWeyl_adjoint_spectral (k : Fin 4) :
    (matrixLineWeyl k)ᴴ = ∑ b, star (matrixLineEigenvalue k b) • qutritMUBProjection k b := by
  rw [matrixLineWeyl_spectral, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_smul, (qutritMUBProjection_positive k b).isHermitian.eq]

private theorem complex_add_adjoint (z : ℂ) : z + star z = ((2 * z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [two_mul]

/-- On each marked plane the real Weyl pair is diagonal in the corresponding qutrit basis. -/
theorem matrixLineWeyl_pair_synthesis (k : Fin 4) (z : ℂ) :
    z • matrixLineWeyl k + star z • (matrixLineWeyl k)ᴴ =
      matrixFrameSynthesis k (fun b => 2 * (z * matrixLineEigenvalue k b).re) := by
  conv_lhs =>
    congr
    · rw [matrixLineWeyl_spectral]
    · rw [matrixLineWeyl_adjoint_spectral]
  change z • (∑ b, matrixLineEigenvalue k b • qutritMUBProjection k b) +
    star z • (∑ b, star (matrixLineEigenvalue k b) • qutritMUBProjection k b) = _
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  change (∑ b : Fin 3, (z • (matrixLineEigenvalue k b • qutritMUBProjection k b) +
      star z • (star (matrixLineEigenvalue k b) • qutritMUBProjection k b))) =
    (∑ b : Fin 3, (2 * (z * matrixLineEigenvalue k b).re : ℝ) • qutritMUBProjection k b)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, ← add_smul, mul_comm (star z), ← star_mul, complex_add_adjoint]
  rfl
private theorem signedExtend_planePair (p : SignedPlaneIndex) (z : ℂ) :
    signedExtend (signedPlaneInclusion p z) =
      z • chargeBasisVector p.val.val + star z • chargeBasisVector (-p.val.val) := by
  funext q
  by_cases hq : q = 0
  · subst q
    simp [chargeBasisVector, Ne.symm p.val.property, Ne.symm (neg_ne_zero.mpr p.val.property)]
  · let u : NonzeroCharge := ⟨q, hq⟩
    obtain ⟨⟨r, b⟩, hb⟩ := signedPlaneGradeEquiv.surjective u
    have hv : (signedPlaneGradeEquiv (r,b)).val = q := congrArg Subtype.val hb
    rw [← hv, signedExtend_nonzero]
    have he (s : Bool) : (signedPlaneGradeEquiv (r,b)).val =
          (signedPlaneGradeEquiv (p,s)).val ↔ r = p ∧ b = s := by
      constructor
      · intro h
        exact Prod.mk.inj (signedPlaneGradeEquiv.injective (Subtype.ext h))
      · rintro ⟨rfl, rfl⟩
        rfl
    have ha : (signedPlaneGradeEquiv (p,false)).val = p.val.val := rfl
    have hs : (signedPlaneGradeEquiv (p,true)).val = -p.val.val := rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, chargeBasisVector]
    rw [← hs, ← ha]
    simp only [he false, he true]
    cases b <;> by_cases hr : r = p <;>
      simp [signedCoordinates_inclusion_representative,
        hr, eq_comm]

theorem signedPlaneInclusion_matrixLine_coordinates (k : Fin 4) (z : ℂ) :
    gradedTitsCoordinates (signedExtend (signedPlaneInclusion (matrixLineGrade k) z)) =
      (matrixFrameSynthesis k (fun b => 2 * (z * matrixLineEigenvalue k b).re), 0, 0) := by
  have hp : homogeneousTits (matrixLineGrade k).val.val = (matrixLineWeyl k, 0, 0) := rfl
  have hn : -(matrixLineGrade k).val.val = chargeFrom (-matrixLineLabel k) 0 := by
    change -(chargeFrom (matrixLineLabel k) 0) = _
    rw [← neg_zero (G := ZMod 3), chargeFrom_neg, neg_zero]
  have hm : homogeneousTits (-(matrixLineGrade k).val.val) = ((matrixLineWeyl k)ᴴ, 0, 0) := by
    rw [hn]
    change ((weylMatrix (-matrixLineLabel k) : Mat3 ℂ), 0, 0) = ((matrixLineWeyl k)ᴴ, 0, 0)
    exact Prod.ext (weylMatrix_adjoint (matrixLineLabel k)).symm rfl
  simp only [signedExtend_planePair, map_add, map_smul, gradedTitsCoordinates_single, hp, hm,
    Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, matrixLineWeyl_pair_synthesis]

/-- The four actual pilot planes map onto their marked signed coordinate planes. -/
theorem matrixLineEmbed_matrixPlane (k : Fin 4) :
    (matrixPlane k).map matrixLineEmbed.toLinearMap = signedPlane (matrixLineGrade k) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · rintro w ⟨z, rfl⟩
    let w := signedPlaneInclusion (matrixLineGrade k) z
    let u := gradedTitsEquiv w
    let c : Fin 3 → ℝ := fun b => 2 * (z * matrixLineEigenvalue k b).re
    have hcoord : Tits.CompactTitsTraceless.coordinates u = (matrixFrameSynthesis k c, 0, 0) := by
      change Tits.CompactTitsTraceless.coordinates (gradedTitsEquiv w) = _
      rw [gradedTitsEquiv_coordinates]
      exact signedPlaneInclusion_matrixLine_coordinates k z
    have ht := Tits.CompactTitsTraceless.complex_trace_zero u
    rw [hcoord, Tits.trace3_eq_matrixTrace, trace_matrixFrameSynthesis] at ht
    have hc : ∑ b, c b = 0 := Complex.ofReal_eq_zero.mp ht
    let x := TracelessHermitian3.ofMatrix (matrixFrameSynthesis k c)
      (matrixFrameSynthesis_hermitian k c) (by simp [hc])
    refine ⟨x, (mem_matrixPlane_iff k x).mpr (matrixFrameProjection_synthesis k c hc), ?_⟩
    change matrixLineEmbed x = w
    apply gradedTitsEquiv.injective
    rw [gradedTitsEquiv_matrixLineEmbed]
    apply Subtype.ext
    apply Tits.CompactTits.ext
    change Tits.CompactTitsTraceless.coordinates (matrixLineTits x) =
      Tits.CompactTitsTraceless.coordinates u
    rw [matrixLineTits_coordinates, hcoord]
    rfl
  · have hdim := ((matrixPlane k).equivMapOfInjective matrixLineEmbed.toLinearMap
        matrixLineEmbed.injective).finrank_eq
    rw [← hdim, matrixPlane_dim, signedPlane_finrank]


end

end ThirteenPlanes
