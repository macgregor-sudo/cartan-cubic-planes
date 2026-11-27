module

public import ThirteenPlanes.Cartan.QuaternionicTorus
public import ThirteenPlanes.Quaternionic.Quartic

@[expose] public section

set_option backward.privateInPublic true

/-! The standard rank-three torus on skew-Hermitian quaternionic matrices. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped Matrix

noncomputable section

def quaternionicStandardDiagonal : (Fin 3 → ℝ) →ₗ[ℝ] QMat where
  toFun a := Matrix.diagonal (fun k => a k • qi)
  map_add' a b := by
    rw [Matrix.diagonal_add]
    congr 1
    funext k
    exact add_smul _ _ _
  map_smul' r a := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext k
    exact mul_smul _ _ _

def quaternionicPullback (U : QBasis) : QMat ≃ₗ[ℝ] QMat where
  toFun A := U.matᴴ * A * U.mat
  invFun A := U.mat * A * U.matᴴ
  left_inv A := by
    simp only [mul_assoc, U.mul_adjoint, mul_one]
    rw [← mul_assoc, U.mul_adjoint, one_mul]
  right_inv A := by
    simp only [mul_assoc, U.adjoint_mul, mul_one]
    rw [← mul_assoc, U.adjoint_mul, one_mul]
  map_add' A B := by simp only [mul_add, add_mul]
  map_smul' r A := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

private theorem diagonal_injective : Function.Injective quaternionicStandardDiagonal := by
  intro a b h
  funext k
  have h' := congrArg (fun A : QMat => (A k k).imI) h
  change ((Matrix.diagonal _ : QMat) k k).imI = ((Matrix.diagonal _ : QMat) k k).imI at h'
  simpa [Matrix.diagonal_apply_eq, qi] using h'

theorem quaternionicStandardDiagonal_dim : Module.finrank ℝ quaternionicStandardDiagonal.range = 3 := by
  rw [LinearMap.finrank_range_of_inj diagonal_injective, Module.finrank_pi_fintype]
  simp

private theorem quaternionicStandardDiagonal_skew (a : Fin 3 → ℝ) :
    (quaternionicStandardDiagonal a)ᴴ = - quaternionicStandardDiagonal a := by
  simp only [quaternionicStandardDiagonal, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext k
  change star (a k • qi) = -(a k • qi)
  rw [Quaternion.star_smul, show star qi = -qi by ext <;> simp [qi], smul_neg]

private theorem quaternionicDiagonals_commute (a b : Fin 3 → ℝ) :
    Commute (quaternionicStandardDiagonal a) (quaternionicStandardDiagonal b) := by
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  change (a k • qi) * (b k • qi) = (b k • qi) * (a k • qi)
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_comm]

private theorem conjugates_into_diagonal (S : Submodule ℝ QMat) (hs : ∀ A ∈ S, Aᴴ = -A)
    (hc : ∀ A ∈ S, ∀ B ∈ S, Commute A B) :
    ∃ U : QBasis, S.map (quaternionicPullback U).toLinearMap ≤ quaternionicStandardDiagonal.range := by
  obtain ⟨U,hU⟩ := quaternionicSkew_simultaneousDiagonalization (fun A : S => A.val)
    (fun A => hs _ A.property) (fun A B _ => hc _ A.property _ B.property)
  refine ⟨U, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨a,ha⟩ := hU ⟨A,hA⟩
  exact ⟨a,ha.symm⟩

/-- Every commuting rank-three real space of skew-Hermitian quaternionic matrices
is conjugate to the full standard diagonal torus. -/
theorem quaternionicRankThree_conjugateStandard (S : Submodule ℝ QMat)
    (hs : ∀ A ∈ S, Aᴴ = -A) (hc : ∀ A ∈ S, ∀ B ∈ S, Commute A B)
    (hd : Module.finrank ℝ S = 3) :
    ∃ U : QBasis, S.map (quaternionicPullback U).toLinearMap = quaternionicStandardDiagonal.range := by
  obtain ⟨U,hU⟩ := conjugates_into_diagonal S hs hc
  refine ⟨U, Submodule.eq_of_le_of_finrank_eq hU ?_⟩
  rw [LinearEquiv.finrank_map_eq, hd, quaternionicStandardDiagonal_dim]

/-- Maximality among commuting skew-Hermitian matrices also gives conjugacy,
without using a rank assumption. -/
theorem quaternionicCartan_conjugateStandard (S : Submodule ℝ QMat)
    (hs : ∀ A ∈ S, Aᴴ = -A) (hc : ∀ A ∈ S, ∀ B ∈ S, Commute A B)
    (hmax : ∀ X : QMat, Xᴴ = -X → (∀ Y ∈ S, Commute X Y) → X ∈ S) :
    ∃ U : QBasis, S.map (quaternionicPullback U).toLinearMap = quaternionicStandardDiagonal.range := by
  obtain ⟨U,hU⟩ := conjugates_into_diagonal S hs hc
  refine ⟨U, le_antisymm hU ?_⟩
  rintro _ ⟨a,rfl⟩
  let X := (quaternionicPullback U).symm (quaternionicStandardDiagonal a)
  have hp : (quaternionicPullback U) X = quaternionicStandardDiagonal a :=
    (quaternionicPullback U).apply_symm_apply _
  have hx : Xᴴ = -X := by
    change (U.mat * quaternionicStandardDiagonal a * U.matᴴ)ᴴ = -(U.mat * quaternionicStandardDiagonal a * U.matᴴ)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      quaternionicStandardDiagonal_skew, neg_mul, mul_neg, mul_assoc]
  refine ⟨X, hmax _ hx ?_, hp⟩
  intro Y hY
  obtain ⟨b, hb⟩ := hU (Submodule.mem_map_of_mem hY)
  apply (quaternionicPullback U).injective
  change unitaryConjugate U (X * Y) = unitaryConjugate U (Y * X)
  rw [unitaryConjugate_mul, unitaryConjugate_mul]
  change quaternionicPullback U X * quaternionicPullback U Y =
    quaternionicPullback U Y * quaternionicPullback U X
  change quaternionicStandardDiagonal b = quaternionicPullback U Y at hb
  rw [hp, ← hb]
  exact (quaternionicDiagonals_commute a b).eq

end
end ThirteenPlanes.Cartan
