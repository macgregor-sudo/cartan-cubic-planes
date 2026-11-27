module

public import ThirteenPlanes.MinimumHessian.Formula
public import ThirteenPlanes.MinimumHessian.Coords

@[expose] public section

/-! The Hessian and the gradient at algebraic floor data, in coordinates.

If `c` has zero trace vector, `M = m δ` and `S = λ Π`, then
`hessC c d k = (-½ + 3m/2 + 6λ)⟨d,k⟩ + 3λ τd·τk - ¾ Σ(K(d)-K(d)ᵀ)(K(k)-K(k)ᵀ)` and the first variation is
`(-½ + m/2 + 2λ)⟨k,c⟩`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem skewPair_eq (c d k : ι → ι → ι → ℝ) :
    skewPair c d k = 2 * ∑ i, ∑ j, kMat c d i j * kMat c k i j -
      2 * ∑ i, ∑ j, kMat c d i j * kMat c k j i := by
  have e1 : ∑ i, ∑ j, kMat c d j i * kMat c k j i = ∑ i, ∑ j, kMat c d i j * kMat c k i j :=
    Finset.sum_comm
  have e2 : ∑ i, ∑ j, kMat c d j i * kMat c k i j = ∑ i, ∑ j, kMat c d i j * kMat c k j i :=
    Finset.sum_comm
  have : skewPair c d k = ∑ i, ∑ j, kMat c d i j * kMat c k i j -
      ∑ i, ∑ j, kMat c d i j * kMat c k j i - ∑ i, ∑ j, kMat c d j i * kMat c k i j +
      ∑ i, ∑ j, kMat c d j i * kMat c k j i := by
    simp only [skewPair, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [this, e1, e2]; ring

theorem two_tetSum_floor {c : ι → ι → ι → ℝ} {m lam : ℝ} (F : FloorData c m lam)
    {d k : ι → ι → ι → ℝ} (hd : Symm d) (hk : Symm k) :
    2 * tetSum k d c c = lam * (vinner (trVec d) (trVec k) + 2 * cinner d k) -
      ∑ i, ∑ j, kMat c d i j * kMat c k i j := by
  have hS : sq4 c = fun i j a b => lam * piT i j a b := funext fun i => funext fun j =>
    funext fun a => funext fun b => F.hS i j a b
  have h1 := sContract_sq4 F.symm hd hk
  rw [hS, sContract_piT hd hk] at h1
  linarith

/-- The Hessian at algebraic floor data. -/
theorem hessC_floor {c : ι → ι → ι → ℝ} {m lam : ℝ} (F : FloorData c m lam)
    {d k : ι → ι → ι → ℝ} (hd : Symm d) (hk : Symm k) :
    hessC c d k = (-(1 / 2) + 3 / 2 * m + 6 * lam) * cinner d k +
      3 * lam * vinner (trVec d) (trVec k) - 3 / 4 * skewPair c d k := by
  have hT := two_tetSum_floor F hd hk
  have hkd : cinner k d = cinner d k := by simp only [cinner, mul_comm]
  have r1 : ∑ i, ∑ j, kMat c k j i * kMat c d i j = ∑ i, ∑ j, kMat c d i j * kMat c k j i :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have r2 : ∑ i, ∑ j, kMat c k j i * kMat c d j i = ∑ i, ∑ j, kMat c d i j * kMat c k i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hessC, quadSum_kdcc F.hM, quadSum_kcdc, quadSum_kccd, r1, r2, skewPair_eq, hkd]
  linarith

/-- The first variation at algebraic floor data. -/
theorem gradC_floor {c : ι → ι → ι → ℝ} {m lam : ℝ} (F : FloorData c m lam)
    {k : ι → ι → ι → ℝ} (hk : Symm k) :
    -(1 / 2) * cinner k c + 3 / 2 * quadSum k c c c + 2 * tetSum k c c c =
      (-(1 / 2) + m / 2 + 2 * lam) * cinner k c := by
  have hT := two_tetSum_floor F F.symm hk
  rw [F.tr] at hT
  have hK : ∑ i, ∑ j, kMat c c i j * kMat c k i j = m * cinner c k := by
    have : ∀ i j, kMat c c i j = m * dlt i j := F.hM
    simp only [this, dlt, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp only [kMat, cinner, Finset.mul_sum]
  have hv : vinner (0 : ι → ℝ) (trVec k) = 0 := by simp [vinner]
  have hkc : cinner c k = cinner k c := by simp only [cinner, mul_comm]
  rw [hv, hK, hkc] at hT
  rw [quadSum_kdcc F.hM]
  linarith

end

end ThirteenPlanes
