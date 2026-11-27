module

public import ThirteenPlanes.MinimumHessian.Invariance
public import ThirteenPlanes.MinimumHessian.Coords

@[expose] public section

/-! The adjoint of the trace map, skew endomorphisms from skew matrices, and coordinate pairings.

`traceAdjoint u` is the cubic `τ*u (x,y,z) = ⅓(⟪x,y⟫⟪u,z⟫ + ⟪x,z⟫⟪u,y⟫ + ⟪y,z⟫⟪u,x⟫)`. In an orthonormal
basis its trace vector is `(n+2)/3 · u`, it pairs with a cubic `k` as `⟪u, τk⟫`, and when the trace
vector of `c` vanishes its mixed contraction `K(τ*u)` with `c` is symmetric. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords

namespace Quartic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate array `⅓(δ_ij w_k + δ_ik w_j + δ_jk w_i)`. -/
def tauAdj (w : ι → ℝ) (i j k : ι) : ℝ := 1 / 3 * (dlt i j * w k + dlt i k * w j + dlt j k * w i)

theorem tauAdj_symm (w : ι → ℝ) : Symm (tauAdj w) := by
  refine ⟨fun i j k => ?_, fun i j k => ?_⟩ <;> simp only [tauAdj] <;>
    simp only [dlt_comm j i, dlt_comm k j, dlt_comm k i] <;> ring

theorem trVec_tauAdj (w : ι → ℝ) (i : ι) : trVec (tauAdj w) i = (dim ι + 2) / 3 * w i := by
  simp [trVec, tauAdj, dlt, Finset.sum_add_distrib, ← Finset.mul_sum, dim]
  ring

theorem cinner_tauAdj {k : ι → ι → ι → ℝ} (hk : Symm k) (w : ι → ℝ) :
    cinner (tauAdj w) k = vinner w (trVec k) := by
  have pt : ∀ x y z, tauAdj w x y z * k x y z = 1 / 3 * (dlt x y * (w z * k x y z)) +
      1 / 3 * (dlt x z * (w y * k x y z)) + 1 / 3 * (dlt y z * (w x * k x y z)) := by
    intro x y z; simp only [tauAdj]; ring
  simp only [cinner, pt, Finset.sum_add_distrib]
  have s1 : ∑ x, ∑ y, ∑ z, dlt x y * (w z * k x y z) = vinner w (trVec k) := by
    simp [dlt, vinner, trVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [hk.s13 x x y]
  have s2 : ∑ x, ∑ y, ∑ z, dlt x z * (w y * k x y z) = vinner w (trVec k) := by
    simp [dlt, vinner, trVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [hk.s12 x y x]
  have s3 : ∑ x, ∑ y, ∑ z, dlt y z * (w x * k x y z) = vinner w (trVec k) := by
    simp [dlt, vinner, trVec, Finset.mul_sum]
  have s1' : ∑ x, ∑ y, ∑ z, 1 / 3 * (dlt x y * (w z * k x y z)) = 1 / 3 * vinner w (trVec k) := by
    rw [← s1]; simp only [Finset.mul_sum]
  have s2' : ∑ x, ∑ y, ∑ z, 1 / 3 * (dlt x z * (w y * k x y z)) = 1 / 3 * vinner w (trVec k) := by
    rw [← s2]; simp only [Finset.mul_sum]
  have s3' : ∑ x, ∑ y, ∑ z, 1 / 3 * (dlt y z * (w x * k x y z)) = 1 / 3 * vinner w (trVec k) := by
    rw [← s3]; simp only [Finset.mul_sum]
  rw [s1', s2', s3']; ring

theorem kMat_tauAdj {c : ι → ι → ι → ℝ} (hc : Symm c) (w : ι → ℝ) (i j : ι) :
    kMat c (tauAdj w) i j = 2 / 3 * ∑ b, c i j b * w b + 1 / 3 * (trVec c i * w j) := by
  have pt : ∀ a b, c i a b * tauAdj w j a b = 1 / 3 * (dlt j a * (c i a b * w b)) +
      1 / 3 * (dlt j b * (c i a b * w a)) + 1 / 3 * (dlt a b * (c i a b * w j)) := by
    intro a b; simp only [tauAdj]; ring
  simp only [kMat, pt, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [dlt, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_ite_eq']
  simp only [trVec, Finset.sum_mul]
  have : ∑ a, c i a j * w a = ∑ b, c i j b * w b :=
    Finset.sum_congr rfl fun a _ => by rw [hc.s23 i a j]
  rw [this]; ring

theorem kMat_tauAdj_symm {c : ι → ι → ι → ℝ} (hc : Symm c) (hv : trVec c = 0) (w : ι → ℝ)
    (i j : ι) : kMat c (tauAdj w) i j = kMat c (tauAdj w) j i := by
  rw [kMat_tauAdj hc, kMat_tauAdj hc, hv]
  simp only [Pi.zero_apply, zero_mul, mul_zero, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [hc.s12 i j b]

omit [DecidableEq ι] in
theorem skewPair_of_symm {c d : ι → ι → ι → ℝ} (h : ∀ i j, kMat c d i j = kMat c d j i)
    (k : ι → ι → ι → ℝ) : skewPair c d k = 0 := by
  simp [skewPair, h]

end Quartic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

/-- The adjoint of the trace map: `τ*u (x,y,z) = ⅓(⟪x,y⟫⟪u,z⟫ + ⟪x,z⟫⟪u,y⟫ + ⟪y,z⟫⟪u,x⟫)`. -/
def traceAdjoint (u : V) : SymmetricCubic V :=
  SymmetricCubic.ofProduct
    (LinearMap.mk₂ ℝ (fun x y => (1 / 3 : ℝ) • (⟪x, y⟫ • u + ⟪u, y⟫ • x + ⟪u, x⟫ • y))
      (fun x x' y => by simp only [inner_add_left, inner_add_right, add_smul, smul_add]; module)
      (fun a x y => by simp only [real_inner_smul_left, real_inner_smul_right, smul_eq_mul]; module)
      (fun x y y' => by simp only [inner_add_left, inner_add_right, add_smul, smul_add]; module)
      (fun a x y => by simp only [real_inner_smul_left, real_inner_smul_right, smul_eq_mul]; module))
    (fun x y => by simp only [LinearMap.mk₂_apply, real_inner_comm x y]; module)
    (fun x y z => by
      simp only [LinearMap.mk₂_apply, real_inner_smul_left, inner_add_left, real_inner_smul_left]
      rw [real_inner_comm y z]
      ring)

theorem coefficient_traceAdjoint (u : V) :
    (traceAdjoint u).coefficient e = tauAdj (fun k => ⟪e k, u⟫) := by
  funext i j k
  have ho := orthonormal_iff_ite.mp e.orthonormal
  simp only [traceAdjoint, SymmetricCubic.coefficient, SymmetricCubic.apply_ofProduct,
    LinearMap.mk₂_apply, real_inner_smul_left, inner_add_left, tauAdj, dlt, ho]
  rw [real_inner_comm u (e k), real_inner_comm u (e j), real_inner_comm u (e i)]
  split_ifs <;> ring

end

end ThirteenPlanes
