module

public import ThirteenPlanes.Quaternionic.RealAction
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! # Actual quaternion lines inside the real column Hilbert space -/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma qInner_mul_left (u v : QVec) (q : Q) :
    qInner (fun i => u i * q) v = star q * qInner u v := by
  simpa only [mul_one] using qInner_right_mul u v q 1

lemma qInner_mul_right (u v : QVec) (q : Q) :
    qInner u (fun i => v i * q) = qInner u v * q := by
  simpa only [mul_one, star_one, one_mul] using qInner_right_mul u v 1 q

lemma qInner_self_real (u : QVec) : qInner u u = ((qInner u u).re : Q) :=
  Quaternion.star_eq_self.mp (qInner_star u u).symm

lemma qInner_self_eq_norm_sq (v : QHilbert) :
    qInner (columnEquiv v) (columnEquiv v) = ((‖v‖ ^ 2 : ℝ) : Q) := by
  calc
    qInner (columnEquiv v) (columnEquiv v)
        = ((qInner (columnEquiv v) (columnEquiv v)).re : Q) := qInner_self_real _
    _ = ((‖v‖ ^ 2 : ℝ) : Q) := by
      rw [← hilbert_inner_eq_qInner_re, real_inner_self_eq_norm_sq]

/-- A real-linear map whose range is the literal right quaternion line vH. -/
def rightLineMap (v : QHilbert) : Q →ₗ[ℝ] QHilbert where
  toFun q := rightMultiply q v
  map_add' p q := by
    apply columnEquiv.injective
    funext i
    change v i * (p + q) = v i * p + v i * q
    exact mul_add _ _ _
  map_smul' r q := by
    apply columnEquiv.injective
    funext i
    change v i * (r • q) = r • (v i * q)
    exact mul_smul_comm _ _ _

def rightLine (v : QHilbert) : Submodule ℝ QHilbert := (rightLineMap v).range

lemma rightLineMap_injective {v : QHilbert} (hv : v ≠ 0) :
    Function.Injective (rightLineMap v) := by
  have hv' : columnEquiv v ≠ 0 := by
    intro h
    apply hv
    apply columnEquiv.injective
    simpa using h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv'
  change v i ≠ 0 at hi
  intro p q h
  have h' := congrArg (fun w : QHilbert => w i) h
  change v i * p = v i * q at h'
  exact mul_left_cancel₀ hi h'

lemma finrank_rightLine {v : QHilbert} (hv : v ≠ 0) :
    Module.finrank ℝ (rightLine v) = 4 := by
  rw [rightLine, LinearMap.finrank_range_of_inj (rightLineMap_injective hv)]
  exact Quaternion.finrank_eq_four

lemma finrank_QHilbert : Module.finrank ℝ QHilbert = 12 := by
  rw [columnEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [Quaternion.finrank_eq_four]

lemma rightLine_le {S : Submodule ℝ QHilbert} (hS : RightStable S)
    {v : QHilbert} (hv : v ∈ S) : rightLine v ≤ S := by
  rintro z ⟨q, rfl⟩
  exact hS v hv q

/-- Real orthogonality to the whole quaternion line is exactly vanishing of the
full quaternion inner product. Testing at q=qInner(v,w) proves the hard direction. -/
lemma mem_rightLine_orthogonal_iff (v w : QHilbert) :
    w ∈ (rightLine v)ᗮ ↔ qInner (columnEquiv v) (columnEquiv w) = 0 := by
  constructor
  · intro hw
    let q := qInner (columnEquiv v) (columnEquiv w)
    have h : inner ℝ (rightMultiply q v) w = 0 := hw _ ⟨q, rfl⟩
    rw [hilbert_inner_eq_qInner_re] at h
    change (qInner (fun i => v i * q) (columnEquiv w)).re = 0 at h
    rw [qInner_mul_left] at h
    change (star q * q).re = 0 at h
    rw [Quaternion.star_mul_self] at h
    exact Quaternion.normSq_eq_zero.mp h
  · intro h
    intro z hz
    obtain ⟨q, rfl⟩ := hz
    rw [hilbert_inner_eq_qInner_re]
    change (qInner (fun i => v i * q) (columnEquiv w)).re = 0
    rw [qInner_mul_left]
    change (star q * qInner (columnEquiv v) (columnEquiv w)).re = 0
    rw [h, mul_zero]
    rfl

lemma rightStable_rightLine_orthogonal (v : QHilbert) : RightStable (rightLine v)ᗮ := by
  intro w hw q
  apply (mem_rightLine_orthogonal_iff v _).mpr
  change qInner (columnEquiv v) (fun i => w i * q) = 0
  rw [qInner_mul_right]
  change qInner (columnEquiv v) (columnEquiv w) * q = 0
  rw [(mem_rightLine_orthogonal_iff v w).mp hw, zero_mul]

lemma rightStable_inf {S T : Submodule ℝ QHilbert}
    (hS : RightStable S) (hT : RightStable T) : RightStable (S ⊓ T) := by
  intro v hv q
  exact ⟨hS v hv.1 q, hT v hv.2 q⟩

lemma rightStable_top : RightStable (⊤ : Submodule ℝ QHilbert) := by
  intro v hv q
  trivial

/-- A common real eigenvector's quaternion line is invariant, since native
matrix action commutes with every right quaternion scalar. -/
lemma rightLine_invariant {A : QMat} {v : QHilbert} {a : ℝ}
    (ha : realAction A v = a • v) : ∀ z ∈ rightLine v, realAction A z ∈ rightLine v := by
  rintro z ⟨q, rfl⟩
  change realAction A (rightMultiply q v) ∈ rightLine v
  rw [realAction_rightMultiply, ha]
  refine ⟨a • q, ?_⟩
  apply columnEquiv.injective
  funext i
  change v i * (a • q) = (a • v i) * q
  rw [mul_smul_comm, smul_mul_assoc]

lemma rightLine_orthogonal_invariant {A : QMat} (hA : A.IsHermitian)
    {v : QHilbert} {a : ℝ} (ha : realAction A v = a • v) :
    ∀ w ∈ (rightLine v)ᗮ, realAction A w ∈ (rightLine v)ᗮ := by
  intro w hw z hz
  rw [← realAction_isSymmetric hA z w]
  exact hw _ (rightLine_invariant ha z hz)

end QuaternionicMUB
