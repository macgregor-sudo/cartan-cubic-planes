module

public import ThirteenPlanes.Quaternionic.JointEigenbasis
public import ThirteenPlanes.Quaternionic.ImaginaryConjugation
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

@[expose] public section

set_option backward.privateInPublic true

/-! Simultaneous unitary diagonalization of commuting quaternionic skew-Hermitian
matrices. Right multiplication by the fixed imaginary unit converts the family
to commuting symmetric real operators on the same twelve-dimensional space. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB Module.End
open scoped BigOperators Matrix

noncomputable section

private def rightI : QHilbert →ₗ[ℝ] QHilbert where
  toFun := rightMultiply qi
  map_add' u v := by ext i : 1; change (_ + _) * qi = _; exact add_mul _ _ _
  map_smul' r v := by ext i : 1; change (r • _) * qi = _; exact smul_mul_assoc _ _ _

private theorem rightI_skew (u v : QHilbert) :
    inner ℝ (rightI u) v = -inner ℝ u (rightI v) := by
  rw [hilbert_inner_eq_qInner_re, hilbert_inner_eq_qInner_re]
  change (qInner (fun k => u k * qi) (columnEquiv v)).re =
    -(qInner (columnEquiv u) (fun k => v k * qi)).re
  rw [qInner_mul_left, qInner_mul_right]
  change (star qi * qInner (columnEquiv u) (columnEquiv v)).re =
    -(qInner (columnEquiv u) (columnEquiv v) * qi).re
  simp [qi]

private theorem action_neg (A : QMat) (u : QHilbert) : realAction (-A) u = - realAction A u := by
  apply columnEquiv.injective
  rw [realAction_apply, map_neg, realAction_apply, matrixAction_apply, matrixAction_apply,
    Matrix.neg_mulVec]

private theorem action_skew {A : QMat} (hA : Aᴴ = -A) (u v : QHilbert) :
    inner ℝ (realAction A u) v = -inner ℝ u (realAction A v) := by
  rw [realAction_adjoint_identity, hA, action_neg, inner_neg_right]

private def rotatedAction (A : QMat) : QHilbert →ₗ[ℝ] QHilbert := rightI.comp (realAction A)

private theorem rotated_symmetric {A : QMat} (hA : Aᴴ = -A) :
    (rotatedAction A).IsSymmetric := by
  intro u v
  change inner ℝ (rightI (realAction A u)) v = inner ℝ u (rightI (realAction A v))
  rw [rightI_skew, action_skew hA, neg_neg]
  change inner ℝ u (realAction A (rightMultiply qi v)) = _
  rw [realAction_rightMultiply]
  rfl

private theorem rotated_commute {A B : QMat} (hAB : Commute A B) :
    Commute (rotatedAction A) (rotatedAction B) := by
  apply LinearMap.ext
  intro v
  change rightMultiply qi (realAction A (rightMultiply qi (realAction B v))) =
    rightMultiply qi (realAction B (rightMultiply qi (realAction A v)))
  rw [realAction_rightMultiply, realAction_rightMultiply]
  have h := LinearMap.congr_fun (realAction_commute hAB).eq v
  exact congrArg (fun x => rightMultiply qi (rightMultiply qi x)) h

private theorem eigen_right {A : QMat} {v : QHilbert} {a : ℝ} (h : rotatedAction A v = a • v) :
    realAction A v = rightMultiply ((-a) • qi) v := by
  ext k : 1
  have hv := congrArg (fun w : QHilbert => w k) h
  change realAction A v k * qi = a • v k at hv
  change realAction A v k = v k * ((-a) • qi)
  have hm := congrArg (fun q : Q => q * qi) hv
  simp only [mul_assoc, qi_sq, mul_neg, mul_one, smul_mul_assoc] at hm
  rw [mul_smul_comm, neg_smul]
  exact (neg_eq_iff_eq_neg.mp hm)

private theorem invariant_complement {A : QMat} {v : QHilbert} {q : Q}
    (hA : Aᴴ = -A) (hv : realAction A v = rightMultiply q v) :
    ∀ w ∈ (rightLine v)ᗮ, realAction A w ∈ (rightLine v)ᗮ := by
  intro w hw z hz
  rw [← neg_eq_iff_eq_neg.mpr (action_skew hA z w), neg_eq_zero]
  apply hw
  obtain ⟨p, rfl⟩ := hz
  change realAction A (rightMultiply p v) ∈ rightLine v
  rw [realAction_rightMultiply, hv]
  refine ⟨q * p, ?_⟩
  ext k : 1
  exact (mul_assoc _ _ _).symm

/-- Every nonzero invariant quaternionic subspace contains a common unit column with
all right eigenvalues in the same fixed imaginary axis. -/
private theorem selectColumn {ι : Type*} (A : ι → QMat) (hA : ∀ i, (A i)ᴴ = -A i)
    (hcomm : Pairwise fun i j => Commute (A i) (A j))
    (S : Submodule ℝ QHilbert) (hS : S ≠ ⊥) (hr : RightStable S)
    (hinv : ∀ i v, v ∈ S → realAction (A i) v ∈ S) :
    ∃ v : QHilbert, v ∈ S ∧ ‖v‖ = 1 ∧ ∃ a : ι → ℝ,
      ∀ i, realAction (A i) v = rightMultiply (a i • qi) v := by
  classical
  let := Submodule.nontrivial_iff_ne_bot.mpr hS
  have hkeep (i) (v) (hv : v ∈ S) : rotatedAction (A i) v ∈ S := hr _ (hinv i v hv) _
  let T (i : ι) := (rotatedAction (A i)).restrict (hkeep i)
  have hT (i) : (T i).IsSymmetric := (rotated_symmetric (hA i)).restrict_invariant _
  have hC : Pairwise fun i j => Commute (T i) (T j) :=
    fun _ _ h => LinearMap.restrict_commute (rotated_commute (hcomm h)) _ _
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have hex : ∃ a : ι → ℝ, (⨅ i, eigenspace (T i) (a i)) ≠ ⊥ := by
    by_contra! hz
    simp only [hz, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨a, ha⟩ := hex
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  have hv0 : (w.val : QHilbert) ≠ 0 := fun h => hw0 (Subtype.ext h)
  let t := ‖w.val‖⁻¹
  refine ⟨t • w.val, S.smul_mem t w.property, ?_, fun i => -a i, ?_⟩
  · rw [norm_smul]
    simp [t, hv0]
  · intro i
    apply eigen_right
    rw [map_smul, smul_comm]
    exact congrArg (fun y : QHilbert => t • y)
      (congrArg Subtype.val (mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hw i)))

private theorem ne_bot_of_positive {S : Submodule ℝ QHilbert} (h : 0 < Module.finrank ℝ S) :
    S ≠ ⊥ := by rintro rfl; simp at h

private theorem diagonalizeWithColumns {ι : Type*} (A : ι → QMat)
    (v w z : QHilbert) (nv : ‖v‖ = 1) (nw : ‖w‖ = 1) (nz : ‖z‖ = 1)
    (vw : qInner (columnEquiv v) (columnEquiv w) = 0)
    (vz : qInner (columnEquiv v) (columnEquiv z) = 0)
    (wz : qInner (columnEquiv w) (columnEquiv z) = 0)
    (a b c : ι → ℝ)
    (ea : ∀ i, realAction (A i) v = rightMultiply (a i • qi) v)
    (eb : ∀ i, realAction (A i) w = rightMultiply (b i • qi) w)
    (ec : ∀ i, realAction (A i) z = rightMultiply (c i • qi) z) :
    ∃ U : QBasis, ∀ i, ∃ a : Fin 3 → ℝ, U.matᴴ * A i * U.mat = Matrix.diagonal (fun k => a k • qi) := by
  classical
  let vec : Fin 3 → QHilbert := ![v,w,z]
  have nvec (i : Fin 3) : ‖vec i‖ = 1 := by
    fin_cases i
    · exact nv
    · exact nw
    · exact nz
  have wv : qInner (columnEquiv w) (columnEquiv v) = 0 := by rw [qInner_star, vw, star_zero]
  have zv : qInner (columnEquiv z) (columnEquiv v) = 0 := by rw [qInner_star, vz, star_zero]
  have zw : qInner (columnEquiv z) (columnEquiv w) = 0 := by rw [qInner_star, wz, star_zero]
  have ovec (i j) (hij : i ≠ j) : qInner (columnEquiv (vec i)) (columnEquiv (vec j)) = 0 := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact vw
    · exact vz
    · exact wv
    · exact (hij rfl).elim
    · exact wz
    · exact zv
    · exact zw
    · exact (hij rfl).elim
  let U : QBasis := ⟨matrixOfColumns vec, matrixOfColumns_adjoint_mul vec nvec ovec,
    mul_adjoint_of_adjoint_mul _ (matrixOfColumns_adjoint_mul vec nvec ovec)⟩
  refine ⟨U, fun i => ⟨![a i, b i, c i], ?_⟩⟩
  let l : Fin 3 → ℝ := ![a i, b i, c i]
  have he (j) : realAction (A i) (vec j) = rightMultiply (l j • qi) (vec j) := by
    fin_cases j
    · exact ea i
    · exact eb i
    · exact ec i
  have hm : A i * U.mat = U.mat * Matrix.diagonal (fun k => l k • qi) := by
    ext k j : 1
    rw [Matrix.mul_diagonal]
    exact congrArg (fun x : QHilbert => x k) (he j)
  rw [mul_assoc, hm, ← mul_assoc, U.adjoint_mul, one_mul]

/-- Every commuting family of actual quaternionic skew-Hermitian 3-by-3 matrices is
diagonal in one quaternionic orthonormal basis, with all diagonal entries real
multiples of the prescribed i. -/
theorem quaternionicSkew_simultaneousDiagonalization {ι : Type*} (A : ι → QMat)
    (hA : ∀ i, (A i)ᴴ = -A i) (hC : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ U : QBasis, ∀ i, ∃ a : Fin 3 → ℝ, U.matᴴ * A i * U.mat = Matrix.diagonal (fun k => a k • qi) := by
  classical
  obtain ⟨v, _, nv, a, ea⟩ := selectColumn A hA hC ⊤ top_ne_bot rightStable_top
    (fun _ _ _ => trivial)
  have v0 : v ≠ 0 := by intro h; simp [h] at nv
  let S := (rightLine v)ᗮ
  have ds : Module.finrank ℝ S = 8 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [finrank_rightLine v0, finrank_QHilbert]
  have hs (i) := invariant_complement (hA i) (ea i)
  obtain ⟨w, hw, nw, b, eb⟩ := selectColumn A hA hC S (ne_bot_of_positive (ds.symm ▸ (by decide : 0 < (8 : ℕ))))
    (rightStable_rightLine_orthogonal v) hs
  have w0 : w ≠ 0 := by intro h; simp [h] at nw
  let P := (rightLine w)ᗮ ⊓ S
  have dp : Module.finrank ℝ P = 4 := by
    apply Submodule.finrank_add_inf_finrank_orthogonal' (rightLine_le (rightStable_rightLine_orthogonal v) hw)
    rw [finrank_rightLine w0, ds]
  have hP (i) (x) (hx : x ∈ P) : realAction (A i) x ∈ P :=
    ⟨invariant_complement (hA i) (eb i) _ hx.1, hs i _ hx.2⟩
  obtain ⟨z, hz, nz, c, ec⟩ := selectColumn A hA hC P (ne_bot_of_positive (dp.symm ▸ (by decide : 0 < (4 : ℕ))))
    (rightStable_inf (rightStable_rightLine_orthogonal w) (rightStable_rightLine_orthogonal v)) hP
  exact diagonalizeWithColumns A v w z nv nw nz
    ((mem_rightLine_orthogonal_iff v w).mp hw)
    ((mem_rightLine_orthogonal_iff v z).mp hz.2)
    ((mem_rightLine_orthogonal_iff w z).mp hz.1) a b c ea eb ec

end
end ThirteenPlanes.Cartan
