module

public import ThirteenPlanes.Quartic.Square

@[expose] public section

/-! Coordinate symmetries behind the rotation invariance of the A-function.

For a symmetric cubic array `c` and an array `X`, put `N(X)_ib = X_ixy c_bxy`. The matrices `N(c)`,
`N(ins_c M)` and `N(T(c))` are symmetric, where `ins_c M` inserts `M = M(c)` in each slot of `c` and
`T(c)_ixy = c_ipq c_xqr c_yrp` is the triangle. Contracted with a skew matrix they give zero. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Quartic

open Coords

variable {ι : Type*} [Fintype ι]

/-- `N(X)_ib = X_ixy c_bxy`. -/
def nMat (X c : ι → ι → ι → ℝ) (i b : ι) : ℝ := ∑ x, ∑ y, X i x y * c b x y

/-- Insertion of a matrix in the three slots, `B_di c_dxy + B_dx c_idy + B_dy c_ixd`. -/
def insArr (B : ι → ι → ℝ) (c : ι → ι → ι → ℝ) (i x y : ι) : ℝ :=
  ∑ d, (B d i * c d x y + B d x * c i d y + B d y * c i x d)

/-- The triangle `T(c)_ixy = c_ipq c_xqr c_yrp`. -/
def triArr (c : ι → ι → ι → ℝ) (i x y : ι) : ℝ :=
  ∑ p, ∑ q, ∑ r, c i p q * c x q r * c y r p

theorem skew_sum_zero {A N : ι → ι → ℝ} (hA : ∀ b i, A b i = -A i b) (hN : ∀ i b, N i b = N b i) :
    ∑ i, ∑ b, A b i * N i b = 0 := by
  have h : ∑ i, ∑ b, A b i * N i b = -∑ i, ∑ b, A b i * N i b := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by rw [hA, hN]; ring
  linarith

theorem mMat_symm (c : ι → ι → ι → ℝ) (i j : ι) : mMat c i j = mMat c j i := by
  simp only [mMat, mul_comm]

theorem nMat_self_symm (c : ι → ι → ι → ℝ) (i b : ι) : nMat c c i b = nMat c c b i := by
  simp only [nMat, mul_comm]

theorem nMat_tri_symm {c : ι → ι → ι → ℝ} (hc : Symm c) (i b : ι) :
    nMat (triArr c) c i b = nMat (triArr c) c b i := by
  have L : ∀ i b, nMat (triArr c) c i b = ∑ t : ι × ι × ι × ι × ι,
      c i t.2.2.1 t.2.2.2.1 * c t.1 t.2.2.2.1 t.2.2.2.2 * c t.2.1 t.2.2.2.2 t.2.2.1 *
        c b t.1 t.2.1 := by
    intro i b
    simp only [nMat, triArr, Finset.sum_mul, Fintype.sum_prod_type]
  rw [L, L]
  refine Fintype.sum_equiv
    ⟨fun t => (t.2.2.1, t.2.2.2.1, t.1, t.2.1, t.2.2.2.2),
      fun t => (t.2.2.1, t.2.2.2.1, t.1, t.2.1, t.2.2.2.2), fun _ => rfl, fun _ => rfl⟩
    _ _ fun t => ?_
  obtain ⟨x, y, p, q, r⟩ := t
  simp only [Equiv.coe_fn_mk]
  rw [hc.s12 p y r, hc.s23 y p r, hc.s13 q r x, hc.s23 x r q]
  ring

theorem nMat_ins_symm {c : ι → ι → ι → ℝ} (hc : Symm c) (i b : ι) :
    nMat (insArr (mMat c) c) c i b = nMat (insArr (mMat c) c) c b i := by
  have split : ∀ i b, nMat (insArr (mMat c) c) c i b =
      ∑ d, mMat c d i * mMat c d b +
      (∑ t : ι × ι × ι, mMat c t.2.2 t.1 * c i t.2.2 t.2.1 * c b t.1 t.2.1) +
      (∑ t : ι × ι × ι, mMat c t.2.2 t.2.1 * c i t.1 t.2.2 * c b t.1 t.2.1) := by
    intro i b
    have h1 : ∑ x, ∑ y, ∑ d, mMat c d i * c d x y * c b x y = ∑ d, mMat c d i * mMat c d b := by
      rw [sum3_rot, sum3_rot]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [show mMat c d b = ∑ x, ∑ y, c d x y * c b x y from rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [← h1]
    simp only [nMat, insArr, Finset.sum_mul, add_mul, Finset.sum_add_distrib,
      Fintype.sum_prod_type]
  rw [split, split]
  have t1 : ∑ d, mMat c d i * mMat c d b = ∑ d, mMat c d b * mMat c d i :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have t2 : (∑ t : ι × ι × ι, mMat c t.2.2 t.1 * c i t.2.2 t.2.1 * c b t.1 t.2.1) =
      ∑ t : ι × ι × ι, mMat c t.2.2 t.1 * c b t.2.2 t.2.1 * c i t.1 t.2.1 :=
    Fintype.sum_equiv ⟨fun t => (t.2.2, t.2.1, t.1), fun t => (t.2.2, t.2.1, t.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by
        simp only [Equiv.coe_fn_mk]; rw [mMat_symm c t.2.2 t.1]; ring
  have t3 : (∑ t : ι × ι × ι, mMat c t.2.2 t.2.1 * c i t.1 t.2.2 * c b t.1 t.2.1) =
      ∑ t : ι × ι × ι, mMat c t.2.2 t.2.1 * c b t.1 t.2.2 * c i t.1 t.2.1 :=
    Fintype.sum_equiv ⟨fun t => (t.1, t.2.2, t.2.1), fun t => (t.1, t.2.2, t.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by
        simp only [Equiv.coe_fn_mk]; rw [mMat_symm c t.2.2 t.2.1]; ring
  rw [t1, t2, t3]

end Quartic

end

end ThirteenPlanes
