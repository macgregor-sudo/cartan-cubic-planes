module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RealDerivations

open scoped Matrix BigOperators

noncomputable section

abbrev M₃ := Matrix (Fin 3) (Fin 3) ℝ
abbrev SymmetricThree := selfAdjoint M₃

def jordan (x y : SymmetricThree) : SymmetricThree :=
  ⟨(1 / 2 : ℝ) • (x.val * y.val + y.val * x.val), by
    rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul,
      x.property, y.property, star_trivial, add_comm]⟩

def Derivation (D : Module.End ℝ SymmetricThree) : Prop :=
  ∀ x y, D (jordan x y) = jordan (D x) y + jordan x (D y)

theorem symm (x : SymmetricThree) (i j : Fin 3) : x.val j i = x.val i j := by
  have he := congrArg (fun z : M₃ => z i j) x.property
  simpa [Matrix.star_apply] using he

private def p (i : Fin 3) : SymmetricThree :=
  ⟨Matrix.diagonal (fun j => if j = i then 1 else 0), by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    ext j k
    by_cases h : j = k
    · subst k; rfl
    · simp only [Matrix.transpose_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]⟩

private def off (i j : Fin 3) : SymmetricThree :=
  ⟨Matrix.single i j 1 + Matrix.single j i 1, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    simp [add_comm]⟩

private theorem p_left (i : Fin 3) (x : SymmetricThree) (j k : Fin 3) :
    (jordan (p i) x).val j k = (1 / 2 : ℝ) *
      ((if j = i then x.val j k else 0) + (if k = i then x.val j k else 0)) := by
  change (1 / 2 : ℝ) * (((p i).val * x.val) j k + (x.val * (p i).val) j k) = _
  simp only [p, Matrix.diagonal_mul, Matrix.mul_diagonal]
  split_ifs <;> ring

private theorem p_right (i : Fin 3) (x : SymmetricThree) : jordan x (p i) = jordan (p i) x :=
  Subtype.ext (by change (1 / 2 : ℝ) • _ = (1 / 2 : ℝ) • _; rw [add_comm])

private theorem p_square (i : Fin 3) : jordan (p i) (p i) = p i := by
  apply Subtype.ext
  ext j k
  rw [p_left]
  change (1 / 2 : ℝ) * ((if j = i then (p i).val j k else 0) + _) =
    Matrix.diagonal (fun l => if l = i then (1 : ℝ) else 0) j k
  by_cases h : j = k
  · subst k
    simp only [p, Matrix.diagonal_apply_eq]
    split_ifs <;> norm_num
  · simp [p, Matrix.diagonal_apply_ne _ h]

private theorem p_sum : ∑ i, p i = (1 : SymmetricThree) := by
  apply Subtype.ext
  ext j k
  change (∑ i, (p i).val j k) = (1 : M₃) j k
  by_cases h : j = k
  · subst k
    simp [p]
  · simp [p, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

private theorem jordan_one (x : SymmetricThree) : jordan 1 x = x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (1 * x.val + x.val * 1) = x.val
  rw [one_mul, mul_one, ← two_smul ℝ x.val, smul_smul]
  norm_num

private theorem D_one (D : Module.End ℝ SymmetricThree) (hd : Derivation D) : D 1 = 0 := by
  have he := hd 1 1
  rw [jordan_one, show jordan (D 1) 1 = D 1 from (by
    apply Subtype.ext
    change (1 / 2 : ℝ) • ((D 1).val * 1 + 1 * (D 1).val) = (D 1).val
    rw [one_mul, mul_one, ← two_smul ℝ (D 1).val, smul_smul]
    norm_num), jordan_one] at he
  exact left_eq_add.mp he

private theorem D_p_entry (D : Module.End ℝ SymmetricThree) (hd : Derivation D)
    (i j k : Fin 3) (h : (j = i ∧ k = i) ∨ (j ≠ i ∧ k ≠ i)) :
    (D (p i)).val j k = 0 := by
  have he := hd (p i) (p i)
  rw [p_square, p_right] at he
  have hv := congrArg (fun x : SymmetricThree => x.val j k) he
  change (D (p i)).val j k = (jordan (p i) (D (p i))).val j k +
    (jordan (p i) (D (p i))).val j k at hv
  rw [p_left] at hv
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [ite_eq_left h₁, ite_eq_left h₂] at hv
    linarith
  · rw [ite_eq_right h₁, ite_eq_right h₂] at hv
    linarith

private theorem commutator_symm {T : M₃} (hT : Tᵀ = -T) (x : SymmetricThree) :
    T * x.val - x.val * T ∈ selfAdjoint M₃ := by
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hT]
  have hx : x.valᵀ = x.val := by ext i j; exact symm x i j
  rw [hx, Matrix.mul_neg, Matrix.neg_mul, neg_sub_neg]

def commutator (T : M₃) (hT : Tᵀ = -T) : Module.End ℝ SymmetricThree :=
  LinearMap.codRestrict (selfAdjoint.submodule ℝ M₃)
    (((LinearMap.mul ℝ M₃ T) - ((LinearMap.mul ℝ M₃).flip T)).comp
      (selfAdjoint.submodule ℝ M₃).subtype) (commutator_symm hT)

theorem commutator_apply (T : M₃) (hT : Tᵀ = -T) (x : SymmetricThree) :
    (commutator T hT x).val = T * x.val - x.val * T := rfl

private theorem commutator_derivation (T : M₃) (hT : Tᵀ = -T) :
    Derivation (commutator T hT) := by
  intro x y
  apply Subtype.ext
  change T * ((1 / 2 : ℝ) • (x.val * y.val + y.val * x.val)) -
      ((1 / 2 : ℝ) • (x.val * y.val + y.val * x.val)) * T =
    (1 / 2 : ℝ) • ((T * x.val - x.val * T) * y.val + y.val * (T * x.val - x.val * T)) +
      (1 / 2 : ℝ) • (x.val * (T * y.val - y.val * T) + (T * y.val - y.val * T) * x.val)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ← smul_add]
  congr 1
  noncomm_ring

private theorem off_entry (i j k l : Fin 3) :
    (off i j).val k l = (if k = i ∧ l = j then 1 else 0) +
      (if k = j ∧ l = i then 1 else 0) := by
  change (Matrix.single i j (1 : ℝ) + Matrix.single j i 1 : M₃) k l = _
  simp only [Matrix.add_apply, Matrix.single_apply, eq_comm]

private theorem off_left_i {i j : Fin 3} (hij : i ≠ j) :
    jordan (p i) (off i j) = (1 / 2 : ℝ) • off i j := by
  apply Subtype.ext
  ext k l
  rw [p_left]
  change (1 / 2 : ℝ) * ((if k = i then (off i j).val k l else 0) +
    (if l = i then (off i j).val k l else 0)) = (1 / 2 : ℝ) * (off i j).val k l
  rw [off_entry]
  by_cases hki : k = i <;> by_cases hli : l = i <;>
    by_cases hkj : k = j <;> by_cases hlj : l = j <;> simp_all [Ne.symm hij]

private theorem off_left_j {i j : Fin 3} (hij : i ≠ j) :
    jordan (p j) (off i j) = (1 / 2 : ℝ) • off i j := by
  have he : off i j = off j i := Subtype.ext (add_comm _ _)
  rw [he, off_left_i hij.symm]

private theorem off_square {i j : Fin 3} (hij : i ≠ j) :
    jordan (off i j) (off i j) = p i + p j := by
  apply Subtype.ext
  have he (A : M₃) : (1 / 2 : ℝ) • (A + A) = A := by
    rw [← two_smul ℝ A, smul_smul]; norm_num
  change (1 / 2 : ℝ) • ((off i j).val * (off i j).val + _) = _
  rw [he]
  change (Matrix.single i j (1 : ℝ) + Matrix.single j i 1) *
    (Matrix.single i j 1 + Matrix.single j i 1) = (p i + p j).val
  have h₁ : (Matrix.single i j (1 : ℝ) : M₃) * Matrix.single i j 1 = 0 := by
    apply Matrix.single_mul_single_of_ne
    exact hij.symm
  have h₂ : (Matrix.single j i (1 : ℝ) : M₃) * Matrix.single j i 1 = 0 := by
    apply Matrix.single_mul_single_of_ne
    exact hij
  simp only [add_mul, mul_add, Matrix.single_mul_single_same, h₁, h₂, mul_one, zero_add, add_zero]
  ext k l
  by_cases h : k = l
  · subst l; simp [p, Matrix.single_apply, eq_comm, add_comm]
  · change (Matrix.single j j (1 : ℝ) + Matrix.single i i (1 : ℝ) : M₃) k l =
      (p i).val k l + (p j).val k l
    simp only [p, Matrix.add_apply, Matrix.single_apply, Matrix.diagonal_apply_ne _ h]
    split_ifs <;> simp_all <;> aesop

/- This proves the real symmetric 3×3 case of the derivation description in John Baez,
The Octonions, §4.1, Eq. (19) (arXiv:math/0105155). The skew matrix is constructed
from the action of the derivation on the diagonal idempotents. -/
theorem real_symmetric_derivation_inner (D : Module.End ℝ SymmetricThree) (hd : Derivation D) :
    ∃ (T : M₃) (hT : Tᵀ = -T), D = commutator T hT := by
  let T : M₃ := fun i j => if i = j then 0 else (D (p j)).val i j
  have hsum : ∑ i, D (p i) = 0 := by rw [← map_sum, p_sum, D_one D hd]
  have hT : Tᵀ = -T := by
    ext i j
    change (if j = i then 0 else (D (p i)).val j i) =
      -(if i = j then 0 else (D (p j)).val i j)
    by_cases hij : i = j
    · subst j; simp
    · have hv := congrArg (fun x : SymmetricThree => x.val i j) hsum
      change (∑ k, (D (p k)).val i j) = 0 at hv
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k => k = i ∨ k = j)] at hv
      have hzero : ∑ k ∈ Finset.univ.filter (fun k => ¬ (k = i ∨ k = j)),
          (D (p k)).val i j = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have h := not_or.mp (Finset.mem_filter.mp hk).2
        exact D_p_entry D hd k i j (Or.inr ⟨Ne.symm h.1, Ne.symm h.2⟩)
      rw [hzero, add_zero] at hv
      have hfilter : (Finset.univ.filter (fun k : Fin 3 => k = i ∨ k = j)) = {i, j} := by
        ext k; simp
      rw [hfilter, Finset.sum_pair hij] at hv
      rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), symm (D (p i))]
      linarith only [hv]
  let C := commutator T hT
  have hp (i : Fin 3) : C (p i) = D (p i) := by
    apply Subtype.ext
    ext j k
    rw [commutator_apply]
    conv_lhs => simp only [p, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hj : j = i <;> by_cases hk : k = i
    · subst j; subst k
      rw [D_p_entry D hd i i i (Or.inl ⟨rfl, rfl⟩)]
      simp [T]
    · subst j
      simp [hk, T, Ne.symm hk]
      have hh := congrArg (fun M : M₃ => M i k) hT
      change T k i = -T i k at hh
      simp [T, hk, Ne.symm hk] at hh
      rw [symm (D (p i)) i k] at hh
      exact hh.symm
    · subst k; simp [T, hj]
    · simp [hj, hk, D_p_entry D hd i j k (Or.inr ⟨hj, hk⟩)]
  let E := D - C
  have hE : Derivation E := by
    have hc := commutator_derivation T hT
    intro x y
    change D (jordan x y) - C (jordan x y) =
      jordan (D x - C x) y + jordan x (D y - C y)
    rw [hd, hc x y]
    apply Subtype.ext
    change ((jordan (D x) y).val + (jordan x (D y)).val) -
      ((jordan (C x) y).val + (jordan x (C y)).val) = _
    simp only [jordan, AddSubgroup.coe_add, AddSubgroup.coe_sub, sub_mul, mul_sub, smul_sub, smul_add]
    abel
  have E_p (i : Fin 3) : E (p i) = 0 := sub_eq_zero.mpr (hp i).symm
  have E_off (i j : Fin 3) (hij : i ≠ j) : E (off i j) = 0 := by
    let y := E (off i j)
    have hleft (k : Fin 3) (hk : k = i ∨ k = j) : (1 / 2 : ℝ) • y = jordan (p k) y := by
      have hv := hE (p k) (off i j)
      have he : jordan (p k) (off i j) = (1 / 2 : ℝ) • off i j := by
        rcases hk with rfl | rfl
        · exact off_left_i hij
        · exact off_left_j hij
      rw [he, map_smul, E_p] at hv
      have hz : jordan 0 (off i j) = 0 := Subtype.ext (by simp [jordan])
      rwa [hz, zero_add] at hv
    have hy_zero (a b : Fin 3) (h₀ : ¬ (a = i ∧ b = j)) (h₁ : ¬ (a = j ∧ b = i)) :
        y.val a b = 0 := by
      by_contra hn
      have hone (k : Fin 3) (hk : k = i ∨ k = j) : a = k ∨ b = k := by
        have hh := congrArg (fun x : SymmetricThree => x.val a b) (hleft k hk)
        rw [p_left] at hh
        change (1 / 2 : ℝ) * y.val a b = _ at hh
        by_contra! hz
        rw [ite_eq_right hz.1, ite_eq_right hz.2] at hh
        apply hn
        linarith
      rcases hone i (Or.inl rfl) with ha | hb <;>
        rcases hone j (Or.inr rfl) with ha' | hb'
      · exact hij (ha.symm.trans ha')
      · exact h₀ ⟨ha, hb'⟩
      · exact h₁ ⟨ha', hb⟩
      · exact hij (hb.symm.trans hb')
    have hy : y = y.val i j • off i j := by
      apply Subtype.ext
      ext a b
      change y.val a b = y.val i j * (off i j).val a b
      rw [off_entry]
      by_cases h₁ : a = i ∧ b = j
      · rcases h₁ with ⟨rfl, rfl⟩
        simp [hij, Ne.symm hij]
      · by_cases h₂ : a = j ∧ b = i
        · rcases h₂ with ⟨rfl, rfl⟩
          simpa [hij, Ne.symm hij] using symm y b a
        · rw [hy_zero a b h₁ h₂]
          simp [h₁, h₂]
    have hsq := hE (off i j) (off i j)
    rw [off_square hij, map_add, E_p, E_p, add_zero] at hsq
    change 0 = jordan y (off i j) + jordan (off i j) y at hsq
    rw [hy] at hsq
    have hm := congrArg (fun x : SymmetricThree => x.val i i) hsq
    have hp : (p i + p j).val i i = 1 := by simp [p, hij]
    have hcoef : y.val i j = 0 := by
      have he (r : ℝ) : jordan (r • off i j) (off i j) = r • (p i + p j) := by
        rw [← off_square hij]
        apply Subtype.ext
        change (1 / 2 : ℝ) • ((r • (off i j).val) * (off i j).val + (off i j).val * (r • (off i j).val)) =
          r • ((1 / 2 : ℝ) • _)
        rw [smul_mul_assoc, mul_smul_comm, ← smul_add, smul_comm]
      have hc (r : ℝ) : jordan (off i j) (r • off i j) = jordan (r • off i j) (off i j) :=
        Subtype.ext (by change (1 / 2 : ℝ) • _ = (1 / 2 : ℝ) • _; rw [add_comm])
      rw [hc, he] at hm
      change 0 = y.val i j * (p i + p j).val i i + y.val i j * (p i + p j).val i i at hm
      rw [hp] at hm
      linarith only [hm]
    change y = 0
    rw [hy, hcoef, zero_smul]
  have hE₀ : E = 0 := by
    ext x : 1
    have hrep : x = (∑ i, x.val i i • p i) + x.val 0 1 • off 0 1 +
        x.val 0 2 • off 0 2 + x.val 1 2 • off 1 2 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [p, off, Fin.sum_univ_three, symm x] <;>
        exact symm x 0 1
    rw [hrep, map_add, map_add, map_add, map_sum]
    simp [E_p, E_off, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide]
  exact ⟨T, hT, sub_eq_zero.mp hE₀⟩

end
end ThirteenPlanes.RealDerivations
