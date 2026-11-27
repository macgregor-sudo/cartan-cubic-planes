module

public import ThirteenPlanes.Quaternionic.CapacityCorollaries
public import ThirteenPlanes.Quaternionic.QuaternionComplex
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option backward.privateInPublic true

/-! The standard quaternionic antiunitary and projectively invariant bases in complex dimension six. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped BigOperators Matrix

noncomputable section

abbrev ComplexSix := EuclideanSpace ℂ (Fin 3 ⊕ Fin 3)
abbrev ComplexSixBasis := OrthonormalBasis (Fin 6) ℂ ComplexSix

/-- Right multiplication by the quaternionic unit j in the complex coordinates q = a + j b. -/
def quaternionicJ (x : ComplexSix) : ComplexSix :=
  WithLp.toLp 2 (Sum.elim (fun k => -star (x (.inr k))) (fun k => star (x (.inl k))))

def quaternionicColumn (x : ComplexSix) : QVec :=
  fun k => quaternionOfComplexPair (x (.inl k)) (star (x (.inr k)))

theorem quaternionicJ_sq (x : ComplexSix) : quaternionicJ (quaternionicJ x) = -x := by
  ext i
  cases i <;> simp [quaternionicJ]

theorem quaternionicJ_smul (t : ℂ) (x : ComplexSix) :
    quaternionicJ (t • x) = star t • quaternionicJ x := by
  ext i
  cases i <;> simp [quaternionicJ]

private theorem six_inner (u v : ComplexSix) :
    inner ℂ u v = ∑ k : Fin 3, (star (u (.inl k)) * v (.inl k) +
                               star (u (.inr k)) * v (.inr k)) := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type, Finset.sum_add_distrib]
  simp [RCLike.inner_apply, mul_comm]

theorem inner_quaternionicJ_self (u : ComplexSix) : inner ℂ u (quaternionicJ u) = 0 := by
  rw [six_inner]
  apply Finset.sum_eq_zero
  intro k _
  change star _ * (-star _) + star _ * star _ = 0
  ring

private theorem pair_add (a b c d : ℂ) :
    quaternionOfComplexPair (a+c) (b+d) =
      quaternionOfComplexPair a b + quaternionOfComplexPair c d := by ext <;> rfl

private theorem sum_pair {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ∑ k ∈ s, quaternionOfComplexPair (a k) (b k) =
      quaternionOfComplexPair (∑ k ∈ s, a k) (∑ k ∈ s, b k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert i s hi ih => simp only [Finset.sum_insert hi, ih, pair_add]

/-- Both components of the native quaternionic column Gram entry. -/
theorem quaternionicColumn_inner (u v : ComplexSix) :
    qInner (quaternionicColumn u) (quaternionicColumn v) =
      quaternionOfComplexPair (inner ℂ u v) (-inner ℂ u (quaternionicJ v)) := by
  rw [qInner, six_inner, six_inner, ← Finset.sum_neg_distrib, ← sum_pair]
  apply Finset.sum_congr rfl
  intro k _
  simp only [quaternionicColumn, quaternionOfComplexPair_star, quaternionOfComplexPair_mul,
    star_star]
  congr 1 <;> dsimp [quaternionicJ] <;> ring

/-- Equation (7.1) for the ordinary complex and quaternionic inner products. -/
theorem quaternionicOverlap_eq_complexPair (u v : ComplexSix) :
    Quaternion.normSq (qInner (quaternionicColumn u) (quaternionicColumn v)) =
      Complex.normSq (inner ℂ u v) + Complex.normSq (inner ℂ u (quaternionicJ v)) := by
  rw [quaternionicColumn_inner, quaternionOfComplexPair_normSq, Complex.normSq_neg]

/-- Each standard J-image is an element of the basis up to a complex phase. -/
def IsProjectivelyJInvariant (B : ComplexSixBasis) : Prop :=
  ∀ i, ∃ (j : Fin 6) (z : ℂ), Complex.normSq z = 1 ∧ quaternionicJ (B i) = z • B j

def ComplexSixUnbiased (B C : ComplexSixBasis) : Prop :=
  ∀ i j, Complex.normSq (inner ℂ (B i) (C j)) = 1 / 6

private theorem basis_inner (B : ComplexSixBasis) (i j : Fin 6) :
    inner ℂ (B i) (B j) = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp B.orthonormal i j

/-- Of three representatives of the J-pairs, the lower index of each pair is chosen. -/
private theorem paired_indices (p : Fin 6 → Fin 6) (hp : Function.Involutive p)
    (hne : ∀ i, p i ≠ i) :
    ∃ a : Fin 3 ↪ Fin 6, ∀ i j, a i ≠ p (a j) := by
  let L := {i : Fin 6 // i < p i}
  let H := {i : Fin 6 // ¬ i < p i}
  let swap : L ≃ H :=
    { toFun := fun i => ⟨p i, by rw [hp]; exact not_lt_of_ge i.property.le⟩
      invFun := fun i => ⟨p i, by rw [hp]; exact lt_of_le_of_ne (le_of_not_gt i.property) (hne _)⟩
      left_inv := fun i => Subtype.ext (hp i)
      right_inv := fun i => Subtype.ext (hp i) }
  have hsum := Fintype.card_congr (Equiv.sumCompl (fun i : Fin 6 => i < p i))
  change Fintype.card (L ⊕ H) = Fintype.card (Fin 6) at hsum
  rw [Fintype.card_sum, Fintype.card_fin, ← Fintype.card_congr swap] at hsum
  have hL : Fintype.card L = 3 := by omega
  let e := (Fintype.equivFinOfCardEq hL).symm
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype _), ?_⟩
  intro i j hij
  change (e i : Fin 6) = p (e j) at hij
  have hi := (e i).property
  rw [hij, hp] at hi
  exact (lt_asymm hi (e j).property)

private theorem paired_basis (B : ComplexSixBasis) (hB : IsProjectivelyJInvariant B) :
    ∃ (a : Fin 3 ↪ Fin 6) (U : QBasis), ∀ i, U.column i = quaternionicColumn (B (a i)) := by
  choose p z hz hJ using fun i => hB i
  have hz0 (i) : z i ≠ 0 := by intro h; have hh := hz i; simp [h] at hh
  have hne (i) : p i ≠ i := by
    intro hi
    have h := inner_quaternionicJ_self (B i)
    rw [hJ, hi, inner_smul_right, basis_inner, ite_eq_left rfl, mul_one] at h
    exact hz0 i h
  have hp : Function.Involutive p := by
    intro i
    by_contra hi
    have h := quaternionicJ_sq (B i)
    rw [hJ i, quaternionicJ_smul, hJ (p i)] at h
    apply_fun (fun x => inner ℂ (B i) x) at h
    simp only [inner_smul_right, inner_neg_right, basis_inner, ite_eq_right (Ne.symm hi), mul_zero] at h
    norm_num at h
  obtain ⟨a, ha⟩ := paired_indices p hp hne
  let M : QMat := fun k i => quaternionicColumn (B (a i)) k
  have hM : Mᴴ * M = 1 := by
    ext i j : 1
    change qInner (quaternionicColumn (B (a i))) (quaternionicColumn (B (a j))) = _
    rw [quaternionicColumn_inner, hJ, inner_smul_right, basis_inner, basis_inner,
      ite_eq_right (ha i j), mul_zero, neg_zero, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, ite_eq_left rfl]
      ext <;> simp [quaternionOfComplexPair]
    · rw [ite_eq_right (fun h => hij (a.injective h)), ite_eq_right hij]
      ext <;> simp [quaternionOfComplexPair]
  exact ⟨a, ⟨M, hM, mul_adjoint_of_adjoint_mul M hM⟩, fun _ => rfl⟩

private theorem noSixInvariantBases (B : Fin 6 → ComplexSixBasis)
    (hinv : ∀ i, IsProjectivelyJInvariant (B i))
    (hmut : Pairwise fun i j => ComplexSixUnbiased (B i) (B j)) : False := by
  choose a U hU using fun i => paired_basis (B i) (hinv i)
  apply no_six_of_extension_and_no_seven six_bases_extend no_seven_native_bases U
  intro i j hij s t
  rw [hU, hU, quaternionicOverlap_eq_complexPair]
  obtain ⟨k, z, hz, hJ⟩ := hinv j (a j t)
  rw [hJ, inner_smul_right, map_mul, hz, hmut hij, hmut hij]
  norm_num

/-- Corollary 7. Every set of pairwise unbiased complex bases whose rays are preserved by
the fixed quaternionic antiunitary is finite and has at most five elements. -/
theorem atMostFiveQuaternionicInvariantBases (S : Set ComplexSixBasis)
    (hinv : ∀ B ∈ S, IsProjectivelyJInvariant B) (hmut : S.Pairwise ComplexSixUnbiased) :
    S.Finite ∧ S.ncard ≤ 5 := by
  have hno (e : Fin 6 ↪ S) : False := noSixInvariantBases (fun i => (e i).val)
    (fun i => hinv _ (e i).property)
    (fun _ _ hij => hmut (e _).property (e _).property (fun h => hij (e.injective (Subtype.ext h))))
  have hfinite : S.Finite := by
    by_contra h
    exact hno (Fin.valEmbedding.trans (Set.Infinite.natEmbedding S h))
  refine ⟨hfinite, ?_⟩
  let := hfinite.fintype
  by_contra h
  have hc : Fintype.card (Fin 6) ≤ Fintype.card S := by
    rw [Fintype.card_fin, Set.fintypeCard_eq_ncard]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  exact hno e

end
end ThirteenPlanes.Cartan
