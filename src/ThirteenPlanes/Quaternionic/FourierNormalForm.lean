module

public import ThirteenPlanes.Quaternionic.GeometricFloor

@[expose] public section

/-! The quaternionic normal form with independent column reorderings. -/

namespace QuaternionicMUB

open scoped BigOperators Matrix

noncomputable section

/-- Reindex the columns of a native quaternionic orthonormal basis. -/
def QBasis.permuteOutcomes (U : QBasis) (e : Equiv.Perm Outcome) : QBasis where
  mat i j := U.mat i (e j)
  adjoint_mul := by
    apply Matrix.ext
    intro i j
    have he := congrArg (fun M : QMat => M (e i) (e j)) U.adjoint_mul
    change (∑ k, star (U.mat k (e i)) * U.mat k (e j)) = (1 : QMat) i j
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      e.injective.eq_iff] using he
  mul_adjoint := by
    apply Matrix.ext
    intro i j
    change (∑ k, U.mat i (e k) * star (U.mat j (e k))) = (1 : QMat) i j
    rw [Equiv.sum_comp e (fun k => U.mat i k * star (U.mat j k))]
    exact congrArg (fun M : QMat => M i j) U.mul_adjoint

@[simp] theorem QBasis.permuteOutcomes_refl (U : QBasis) :
    U.permuteOutcomes (Equiv.refl Outcome) = U := QBasis.eq_of_mat_eq rfl

theorem QBasis.MutuallyUnbiased.permuteOutcomes {U V : QBasis}
    (h : U.MutuallyUnbiased V) (e f : Equiv.Perm Outcome) :
    (U.permuteOutcomes e).MutuallyUnbiased (V.permuteOutcomes f) :=
  fun a b => h (e a) (f b)

/-- Reordering the three frames' outcomes leaves their centered trace weight invariant. -/
theorem basisS_permuteOutcomes (U V W : QBasis) (e f g : Equiv.Perm Outcome) :
    basisS (U.permuteOutcomes e) (V.permuteOutcomes f) (W.permuteOutcomes g) = basisS U V W := by
  let T (a b c : Outcome) := centeredTensor U.point V.point W.point a b c ^ 2
  change 6 * (∑ a, ∑ b, ∑ c, T (e a) (f b) (g c)) = 6 * (∑ a, ∑ b, ∑ c, T a b c)
  apply congrArg (fun t : ℝ => (6 : ℝ) * t)
  calc
    _ = ∑ a, ∑ b, ∑ c, T a (f b) (g c) := Equiv.sum_comp e (fun a => ∑ b, ∑ c, T a (f b) (g c))
    _ = ∑ a, ∑ b, ∑ c, T a b (g c) := Finset.sum_congr rfl fun a _ => Equiv.sum_comp f (fun b => ∑ c, T a b (g c))
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Equiv.sum_comp g (fun c => T a b c)

/-- The printed equivalence permits a common left unitary, with independent right phases
and independent column reorderings for each of the three bases. -/
def IsPermutedFourierNormalForm (U V W : QBasis) (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i) = 1) : Prop :=
  ∃ e f g : Equiv.Perm Outcome,
    IsFourierNormalForm (U.permuteOutcomes e) (V.permuteOutcomes f) (W.permuteOutcomes g) p hp

/-- Quaternionic Fourier normal form with the full basis-equivalence relation. -/
/- The order-three quaternionic Hadamard and unbiased-triple normal forms are due to
Oleg Chterental and Dragomir Ž. Đoković (arXiv:0708.4051v1, §4, p. 15, and the proof
of Theorem 5.4, pp. 24–25). This theorem combines the formal Fourier normalization
with the two correlation tests and permits independent column permutations. -/
theorem quaternionicNormalForm_withPermutations :
    (∀ U V W : QBasis, IsUnbiasedTriple U V W →
      ∃ (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i) = 1),
        IsPermutedFourierNormalForm U V W p hp) ∧
    (∀ (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i) = 1),
      IsUnbiasedTriple QBasis.coordinate fourierBasis (phasedFourierBasis p hp) ↔
        Heron.correlation (phaseA p) = 0 ∧ Heron.correlation (phaseB p) = 0) := by
  refine ⟨?_, quaternionicNormalForm.2⟩
  intro U V W h
  obtain ⟨p, hp, hform⟩ := exists_fourierNormalForm U V W h
  exact ⟨p, hp, Equiv.refl _, Equiv.refl _, Equiv.refl _, by simpa only [QBasis.permuteOutcomes_refl]⟩

/-- The equality condition of the sharp quaternionic triple-share bound in every allowed Fourier normal form. -/
theorem quaternionicFloor_equality_withPermutations {U V W : QBasis}
    (h : IsUnbiasedTriple U V W) {p : Outcome → Q} {hp : ∀ i, Quaternion.normSq (p i) = 1}
    (hform : IsPermutedFourierNormalForm U V W p hp) :
    basisGeometricShare U V W = 1 - 1 / Real.sqrt 3 ↔
      Heron.FloorBalanceShape (phaseZ p 0) (phaseZ p 1) (phaseZ p 2) := by
  obtain ⟨e, f, g, hn⟩ := hform
  have hpTriple : IsUnbiasedTriple (U.permuteOutcomes e) (V.permuteOutcomes f)
      (W.permuteOutcomes g) :=
    ⟨h.1.permuteOutcomes e f, h.2.1.permuteOutcomes e g, h.2.2.permuteOutcomes f g⟩
  rw [basisGeometricShare_eq_basisS U V W h.1 h.2.1 h.2.2,
    ← basisS_permuteOutcomes U V W e f g]
  exact nativeTripleFloor.2.2 _ _ _ hpTriple p hp hn

end

end QuaternionicMUB
