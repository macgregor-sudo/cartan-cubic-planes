module

public import ThirteenPlanes.MinimumHessian.TraceAdjoint

@[expose] public section

/-! Skew endomorphisms from skew matrices, the coordinate pairing with infinitesimal rotations,
and nondegeneracy of the coefficient pairing. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

/-- The endomorphism with matrix `Ω` in the basis `e`: `x ↦ Σ Ω_ai ⟪e i, x⟫ e a`. -/
def skewOp (Ω : ι → ι → ℝ) : V →ₗ[ℝ] V :=
  ∑ a, ∑ i, Ω a i • (innerSL ℝ (e i) : V →ₗ[ℝ] ℝ).smulRight (e a)

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem skewOp_apply (Ω : ι → ι → ℝ) (x : V) :
    skewOp e Ω x = ∑ a, ∑ i, (Ω a i * ⟪e i, x⟫) • e a := by
  simp [skewOp, LinearMap.sum_apply, smul_smul]

omit [FiniteDimensional ℝ V] in
theorem matOf_skewOp (Ω : ι → ι → ℝ) (b j : ι) : matOf e (skewOp e Ω) b j = Ω b j := by
  have ho := orthonormal_iff_ite.mp e.orthonormal
  simp [matOf, skewOp_apply, inner_sum, real_inner_smul_right, ho]

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem isSkew_skewOp {Ω : ι → ι → ℝ} (hΩ : ∀ a i, Ω a i = -Ω i a) : IsSkew (skewOp e Ω) := by
  intro x y
  simp only [skewOp_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm (f := fun a i => Ω a i * ⟪e i, y⟫ * ⟪x, e a⟫)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hΩ a i, real_inner_comm x (e i)]
  ring

/-- `⟨D, C.insert A⟩ = 3 Σ A_bi K(D)_bi` with `K(D)_bi = c_bxy d_ixy`. -/
theorem tensorPairing_insert_coord (C D : SymmetricCubic V) (A : V →ₗ[ℝ] V) :
    D.tensorPairing (C.insert A) =
      3 * ∑ i, ∑ b, matOf e A b i * kMat (C.coefficient e) (D.coefficient e) b i := by
  rw [tensorPairing_insert e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [apply_map₁ e C A, Finset.mul_sum]
  rw [sum3_rot, sum3_rot]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [kMat, Finset.mul_sum, coefficient]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] in
theorem eq_zero_of_coefficient (h : SymmetricCubic V) (h0 : ∀ i j k, h.coefficient e i j k = 0) :
    h = 0 := by
  apply ext; intro x y z
  rw [apply_zero, ← e.sum_repr' x, apply_sum₁ e]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [h.apply_swap₁₂, ← e.sum_repr' y, apply_sum₁ e, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [h.apply_swap₂₃, h.apply_swap₁₂, ← e.sum_repr' z, apply_sum₁ e]
  simp only [Finset.mul_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := h0 k j i
  simp only [coefficient] at this
  rw [this]; ring

omit [DecidableEq ι] in
theorem eq_zero_of_tensorPairing_self (h : SymmetricCubic V) (h0 : h.tensorPairing h = 0) :
    h = 0 := by
  let e := stdOrthonormalBasis ℝ V
  rw [tensorPairing_eq_sum e] at h0
  apply eq_zero_of_coefficient e
  intro i j k
  have n3 : ∀ i j, 0 ≤ ∑ k, h.coefficient e i j k * h.coefficient e i j k := fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have n2 : ∀ i, 0 ≤ ∑ j, ∑ k, h.coefficient e i j k * h.coefficient e i j k := fun _ =>
    Finset.sum_nonneg fun _ _ => n3 _ _
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => n2 i).mp h0 i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => n3 i j).mp h1 j (Finset.mem_univ _)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_self_nonneg
    (h.coefficient e i j k)).mp h2 k (Finset.mem_univ _)
  exact mul_self_eq_zero.mp h3

omit [DecidableEq ι] in
/-- The coefficient pairing is nondegenerate. -/
theorem eq_of_tensorPairing (X Y : SymmetricCubic V) (h : ∀ k, X.tensorPairing k = Y.tensorPairing k) :
    X = Y := by
  have hs : ∀ k : SymmetricCubic V, (X - Y).tensorPairing k = X.tensorPairing k - Y.tensorPairing k :=
    fun k => by rw [tensorPairing_comm, tensorPairing_sub_right, tensorPairing_comm k,
      tensorPairing_comm k]
  have := eq_zero_of_tensorPairing_self (X - Y) (by rw [hs, h, sub_self])
  exact sub_eq_zero.mp this

end

end ThirteenPlanes
