module

public import ThirteenPlanes.Quartic.Square

@[expose] public section

/-! Coordinate contractions for the Hessian at a floor cubic.

With `K(d)_ij = c_iab d_jab`: `Q(k,d,c,c) = m⟨k,d⟩` when `M = m δ`, `Q(k,c,d,c) = K(k)_ji K(d)_ij`,
`Q(k,c,c,d) = K(k)_ji K(d)_ji`, and the contraction of `S` with `d_ijn k_kln` is
`K(d)·K(k) + 2 P(k,d,c,c)`, which equals `λ(τd·τk + 2⟨d,k⟩)` when `S = λ Π`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Quartic

open Coords

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Algebraic floor data: a symmetric cubic array with zero trace vector, `M = m δ` and
`S = λ Π`. -/
structure FloorData (c : ι → ι → ι → ℝ) (m lam : ℝ) : Prop where
  symm : Symm c
  tr : trVec c = 0
  hM : ∀ i j, mMat c i j = m * dlt i j
  hS : ∀ i j k l, sq4 c i j k l = lam * piT i j k l

/-- The pairing of the skew parts of `K(d)` and `K(k)`, `Σ (K(d)-K(d)ᵀ)(K(k)-K(k)ᵀ) = 4⟨K_a(d),K_a(k)⟩`. -/
def skewPair (c d k : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (kMat c d i j - kMat c d j i) * (kMat c k i j - kMat c k j i)

theorem quadSum_kdcc {c : ι → ι → ι → ℝ} {m : ℝ} (hM : ∀ i j, mMat c i j = m * dlt i j)
    (k d : ι → ι → ι → ℝ) : quadSum k d c c = m * cinner k d := by
  have h1 : ∀ i x y j, ∑ z, ∑ w, k i x y * d j x y * c j z w * c i z w =
      k i x y * d j x y * (m * dlt j i) := by
    intro i x y j; rw [← hM j i]; simp only [mMat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [quadSum, quadTerm, Fintype.sum_prod_type, h1]
  simp only [cinner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp only [dlt, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

omit [DecidableEq ι] in
theorem quadSum_kcdc (c k d : ι → ι → ι → ℝ) :
    quadSum k c d c = ∑ i, ∑ j, kMat c k j i * kMat c d i j := by
  have : ∑ i, ∑ j, kMat c k j i * kMat c d i j = ∑ t : Six ι,
      c t.2.1 t.2.2.1 t.2.2.2.2.1 * k t.1 t.2.2.1 t.2.2.2.2.1 *
        (c t.1 t.2.2.2.1 t.2.2.2.2.2 * d t.2.1 t.2.2.2.1 t.2.2.2.2.2) := by
    simp only [kMat, Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [this, quadSum]
  exact Fintype.sum_equiv
    ⟨fun t => (t.1, t.2.2.2.1, t.2.1, t.2.2.2.2.1, t.2.2.1, t.2.2.2.2.2),
      fun t => (t.1, t.2.2.1, t.2.2.2.2.1, t.2.1, t.2.2.2.1, t.2.2.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by simp only [Equiv.coe_fn_mk, quadTerm]; ring

omit [DecidableEq ι] in
theorem quadSum_kccd (c k d : ι → ι → ι → ℝ) :
    quadSum k c c d = ∑ i, ∑ j, kMat c k j i * kMat c d j i := by
  have : ∑ i, ∑ j, kMat c k j i * kMat c d j i = ∑ t : Six ι,
      c t.2.1 t.2.2.1 t.2.2.2.2.1 * k t.1 t.2.2.1 t.2.2.2.2.1 *
        (c t.2.1 t.2.2.2.1 t.2.2.2.2.2 * d t.1 t.2.2.2.1 t.2.2.2.2.2) := by
    simp only [kMat, Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [this, quadSum]
  exact Fintype.sum_equiv
    ⟨fun t => (t.1, t.2.2.2.1, t.2.1, t.2.2.2.2.1, t.2.2.1, t.2.2.2.2.2),
      fun t => (t.1, t.2.2.1, t.2.2.2.2.1, t.2.1, t.2.2.2.1, t.2.2.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by simp only [Equiv.coe_fn_mk, quadTerm]; ring

/-- The contraction of a quartic array with `d_ijn k_kln`. -/
def sContract (S : ι → ι → ι → ι → ℝ) (d k : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ a, ∑ b, S i j a b * ∑ n, d i j n * k a b n

omit [DecidableEq ι] in
theorem sContract_sq4 {c d k : ι → ι → ι → ℝ} (hc : Symm c) (hd : Symm d) (hk : Symm k) :
    sContract (sq4 c) d k = ∑ i, ∑ j, kMat c d i j * kMat c k i j + 2 * tetSum k d c c := by
  have split : sContract (sq4 c) d k =
      (∑ t : Six ι, c t.1 t.2.1 t.2.2.2.2.1 * c t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 *
        (d t.1 t.2.1 t.2.2.2.2.2 * k t.2.2.1 t.2.2.2.1 t.2.2.2.2.2)) +
      (∑ t : Six ι, c t.1 t.2.2.1 t.2.2.2.2.1 * c t.2.1 t.2.2.2.1 t.2.2.2.2.1 *
        (d t.1 t.2.1 t.2.2.2.2.2 * k t.2.2.1 t.2.2.2.1 t.2.2.2.2.2)) +
      (∑ t : Six ι, c t.1 t.2.2.2.1 t.2.2.2.2.1 * c t.2.1 t.2.2.1 t.2.2.2.2.1 *
        (d t.1 t.2.1 t.2.2.2.2.2 * k t.2.2.1 t.2.2.2.1 t.2.2.2.2.2)) := by
    simp only [sContract, sq4, Finset.sum_mul_sum, add_mul, Finset.sum_add_distrib,
      Fintype.sum_prod_type]
  have t1 : (∑ t : Six ι, c t.1 t.2.1 t.2.2.2.2.1 * c t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 *
      (d t.1 t.2.1 t.2.2.2.2.2 * k t.2.2.1 t.2.2.2.1 t.2.2.2.2.2)) =
      ∑ i, ∑ j, kMat c d i j * kMat c k i j := by
    have : ∑ i, ∑ j, kMat c d i j * kMat c k i j = ∑ t : Six ι,
        c t.1 t.2.2.1 t.2.2.2.2.1 * d t.2.1 t.2.2.1 t.2.2.2.2.1 *
          (c t.1 t.2.2.2.1 t.2.2.2.2.2 * k t.2.1 t.2.2.2.1 t.2.2.2.2.2) := by
      simp only [kMat, Finset.sum_mul_sum, Fintype.sum_prod_type]
    rw [this]
    refine Fintype.sum_equiv
      ⟨fun t => (t.2.2.2.2.1, t.2.2.2.2.2, t.1, t.2.2.1, t.2.1, t.2.2.2.1),
        fun t => (t.2.2.1, t.2.2.2.2.1, t.2.2.2.1, t.2.2.2.2.2, t.1, t.2.1),
        fun _ => rfl, fun _ => rfl⟩ _ _ fun t => ?_
    obtain ⟨i, j, a, b, m, n⟩ := t
    simp only [Equiv.coe_fn_mk]
    rw [hc.s12 m i j, hc.s23 i m j, hd.s12 n i j, hd.s23 i n j, hc.s12 m a b, hc.s23 a m b,
      hk.s12 n a b, hk.s23 a n b]
    ring
  have t2 : (∑ t : Six ι, c t.1 t.2.2.1 t.2.2.2.2.1 * c t.2.1 t.2.2.2.1 t.2.2.2.2.1 *
      (d t.1 t.2.1 t.2.2.2.2.2 * k t.2.2.1 t.2.2.2.1 t.2.2.2.2.2)) = tetSum k d c c := by
    rw [tetSum]
    refine Fintype.sum_equiv
      ⟨fun t => (t.2.2.2.2.2, t.2.2.1, t.2.2.2.1, t.2.1, t.1, t.2.2.2.2.1),
        fun t => (t.2.2.2.2.1, t.2.2.2.1, t.2.1, t.2.2.1, t.2.2.2.2.2, t.1),
        fun _ => rfl, fun _ => rfl⟩ _ _ fun t => ?_
    obtain ⟨i, j, a, b, m, n⟩ := t
    simp only [Equiv.coe_fn_mk, tetTerm]
    rw [hk.s12 n a b, hk.s23 a n b, hd.s13 n j i, hc.s12 a i m, hc.s13 b m j, hc.s23 j m b]
    ring
  have t3 : (∑ t : Six ι, c t.1 t.2.2.2.1 t.2.2.2.2.1 * c t.2.1 t.2.2.1 t.2.2.2.2.1 *
      (d t.1 t.2.1 t.2.2.2.2.2 * k t.2.2.1 t.2.2.2.1 t.2.2.2.2.2)) = tetSum k d c c := by
    rw [tetSum]
    refine Fintype.sum_equiv
      ⟨fun t => (t.2.2.2.2.2, t.2.2.2.1, t.2.2.1, t.2.1, t.1, t.2.2.2.2.1),
        fun t => (t.2.2.2.2.1, t.2.2.2.1, t.2.2.1, t.2.1, t.2.2.2.2.2, t.1),
        fun _ => rfl, fun _ => rfl⟩ _ _ fun t => ?_
    obtain ⟨i, j, a, b, m, n⟩ := t
    simp only [Equiv.coe_fn_mk, tetTerm]
    rw [hk.s13 n b a, hd.s13 n j i, hc.s12 b i m, hc.s13 a m j, hc.s23 j m a]
    ring
  rw [split, t1, t2, t3]; ring

theorem sContract_piT {d k : ι → ι → ι → ℝ} (hd : Symm d) (hk : Symm k) (lam : ℝ) :
    sContract (fun i j a b => lam * piT i j a b) d k =
      lam * (vinner (trVec d) (trVec k) + 2 * cinner d k) := by
  simp only [sContract, piT, dlt, mul_add, add_mul, Finset.sum_add_distrib]
  simp [Finset.mul_sum]
  have e1 : ∑ x, ∑ y, ∑ z, lam * (d x x z * k y y z) = lam * vinner (trVec d) (trVec k) := by
    rw [sum3_rot, sum3_rot]
    simp only [vinner, trVec, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by
      rw [hd.s13 x x z, hk.s13 y y z]
  have e2 : ∑ x, ∑ y, ∑ z, lam * (d x y z * k y x z) = lam * cinner d k := by
    simp only [cinner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => by rw [hk.s12 y x z]
  have e3 : ∑ x, ∑ y, ∑ z, lam * (d x y z * k x y z) = lam * cinner d k := by
    simp only [cinner, Finset.mul_sum]
  rw [e1, e2, e3]; ring

end Quartic

end

end ThirteenPlanes
