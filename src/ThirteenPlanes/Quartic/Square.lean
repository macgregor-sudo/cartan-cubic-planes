module

public import ThirteenPlanes.Quartic.Tensor
public import ThirteenPlanes.Potential.Coords

@[expose] public section

/-! The symmetrized quartic tensor of a cubic array.

For a fully symmetric cubic array `c`, `S_ijkl = c_ijm c_klm + c_ikm c_jlm + c_ilm c_jkm` is fully
symmetric, `|S|² = 3 tr M² + 6 P` (each term has squared norm `tr M²`, each pair of terms has inner
product the tetrahedron `P`), `S_ijkk = 2 M_ij + c_ijm v_m`, `tr S = 2x + |v|²` and
`S(φ,φ,φ,φ) = 3 Σ_m (c_ijm φ_i φ_j)²`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Quartic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Coords

/-- One term `A_ijkl = c_ijm c_klm` of the symmetrized quartic tensor. -/
def pairT (c : ι → ι → ι → ℝ) (i j k l : ι) : ℝ := ∑ m, c i j m * c k l m

omit [DecidableEq ι] in
theorem sq4_eq_pairT (c : ι → ι → ι → ℝ) (i j k l : ι) :
    sq4 c i j k l = pairT c i j k l + pairT c i k j l + pairT c i l j k := by
  simp only [sq4, pairT, Finset.sum_add_distrib]

/-! Four-index sums are invariant under permuting the summation variables. -/

omit [DecidableEq ι] in
theorem sum4_swap23 (f : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f i k j l :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [DecidableEq ι] in
theorem sum4_swap34 (f : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f i j l k :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [DecidableEq ι] in
theorem sq4_symm {c : ι → ι → ι → ℝ} (hc : Symm c) : QSymm (sq4 c) := by
  refine ⟨fun i j k l => ?_, fun i j k l => ?_, fun i j k l => ?_⟩ <;>
    refine Finset.sum_congr rfl fun m _ => ?_
  · rw [hc.s12 j i m]; ring
  · rw [hc.s12 k j m]; ring
  · rw [hc.s12 l k m]; ring

/-! Six-index flattening. -/

omit [DecidableEq ι] in
theorem sum6_flat (f : ι → ι → ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g =
      ∑ t : Six ι, f t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 := by
  simp only [Fintype.sum_prod_type]

omit [DecidableEq ι] in
theorem qinner_pairT (c : ι → ι → ι → ℝ) :
    qinner (pairT c) (pairT c) = ∑ t : Six ι,
      c t.1 t.2.1 t.2.2.2.2.1 * c t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 *
        (c t.1 t.2.1 t.2.2.2.2.2 * c t.2.2.1 t.2.2.2.1 t.2.2.2.2.2) := by
  simp only [qinner, pairT, Finset.sum_mul_sum, Fintype.sum_prod_type]

omit [DecidableEq ι] in
theorem qinner_pairT_cross (c : ι → ι → ι → ℝ) :
    qinner (pairT c) (fun i j k l => pairT c i k j l) = ∑ t : Six ι,
      c t.1 t.2.1 t.2.2.2.2.1 * c t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 *
        (c t.1 t.2.2.1 t.2.2.2.2.2 * c t.2.1 t.2.2.2.1 t.2.2.2.2.2) := by
  simp only [qinner, pairT, Finset.sum_mul_sum, Fintype.sum_prod_type]

omit [DecidableEq ι] in
/-- `|A|² = tr M²`, written as the double-square sum. -/
theorem qinner_pairT_eq_quadSum {c : ι → ι → ι → ℝ} (hc : Symm c) :
    qinner (pairT c) (pairT c) = quadSum c c c c := by
  rw [qinner_pairT]
  refine Fintype.sum_equiv
    ⟨fun t => (t.2.2.2.2.1, t.1, t.2.1, t.2.2.2.2.2, t.2.2.1, t.2.2.2.1),
      fun t => (t.2.1, t.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2, t.1, t.2.2.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun t => ?_
  obtain ⟨i, j, k, l, m, m'⟩ := t
  simp only [Equiv.coe_fn_mk, quadTerm]
  rw [hc.s12 m i j, hc.s23 i m j, hc.s12 m' i j, hc.s23 i m' j, hc.s12 m' k l, hc.s23 k m' l,
    hc.s12 m k l, hc.s23 k m l]
  ring

omit [DecidableEq ι] in
/-- `⟨A, A_{ikjl}⟩ = P`, written as the tetrahedron sum. -/
theorem qinner_pairT_cross_eq_tetSum {c : ι → ι → ι → ℝ} (hc : Symm c) :
    qinner (pairT c) (fun i j k l => pairT c i k j l) = tetSum c c c c := by
  rw [qinner_pairT_cross]
  refine Fintype.sum_equiv
    ⟨fun t => (t.1, t.2.1, t.2.2.2.2.1, t.2.2.1, t.2.2.2.2.2, t.2.2.2.1),
      fun t => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2.2, t.2.2.1, t.2.2.2.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun t => ?_
  obtain ⟨i, j, k, l, m, m'⟩ := t
  simp only [Equiv.coe_fn_mk, tetTerm]
  rw [hc.s23 j m' l, hc.s13 m l k]
  ring

omit [DecidableEq ι] in
theorem pairT_s12 {c : ι → ι → ι → ℝ} (hc : Symm c) (i j k l : ι) :
    pairT c i j k l = pairT c j i k l :=
  Finset.sum_congr rfl fun m _ => by rw [hc.s12 i j m]

omit [DecidableEq ι] in
theorem pairT_s34 {c : ι → ι → ι → ℝ} (hc : Symm c) (i j k l : ι) :
    pairT c i j k l = pairT c i j l k :=
  Finset.sum_congr rfl fun m _ => by rw [hc.s12 k l m]

omit [DecidableEq ι] in
/-- `|S|² = 3 tr M² + 6 P` in coordinates. -/
theorem qinner_sq4 {c : ι → ι → ι → ℝ} (hc : Symm c) :
    qinner (sq4 c) (sq4 c) = 3 * quadSum c c c c + 6 * tetSum c c c c := by
  set A := pairT c
  have e : qinner (sq4 c) (sq4 c) =
      qinner A A + qinner (fun i j k l => A i k j l) (fun i j k l => A i k j l) +
      qinner (fun i j k l => A i l j k) (fun i j k l => A i l j k) +
      2 * qinner A (fun i j k l => A i k j l) + 2 * qinner A (fun i j k l => A i l j k) +
      2 * qinner (fun i j k l => A i k j l) (fun i j k l => A i l j k) := by
    simp only [qinner, sq4_eq_pairT, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have n1 : qinner (fun i j k l => A i k j l) (fun i j k l => A i k j l) = qinner A A := by
    simp only [qinner]; exact (sum4_swap23 _).symm
  have n2 : qinner (fun i j k l => A i l j k) (fun i j k l => A i l j k) = qinner A A := by
    simp only [qinner]; rw [sum4_swap34, ← sum4_swap23]
  have x2 : qinner A (fun i j k l => A i l j k) = qinner A (fun i j k l => A i k j l) := by
    simp only [qinner]; rw [sum4_swap34]
    simp only [← pairT_s34 hc, A]
  have x3 : qinner (fun i j k l => A i k j l) (fun i j k l => A i l j k) =
      qinner A (fun i j k l => A i k j l) := by
    rw [← x2]; simp only [qinner]; rw [sum4_swap23]
    simp only [← pairT_s34 hc, A]
  rw [e, n1, n2, x2, x3, qinner_pairT_eq_quadSum hc, qinner_pairT_cross_eq_tetSum hc]
  ring

/-! Contractions of `S`. -/

theorem mtrace_mMat (c : ι → ι → ι → ℝ) : mtrace (mMat c) = strength c := rfl

omit [DecidableEq ι] in
theorem contr_sq4 {c : ι → ι → ι → ℝ} (hc : Symm c) (i j : ι) :
    contr (sq4 c) i j = 2 * mMat c i j + ∑ m, c i j m * trVec c m := by
  have h1 : ∑ k, ∑ m, c i j m * c k k m = ∑ m, c i j m * trVec c m := by
    rw [Finset.sum_comm]; simp only [trVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by rw [hc.s13 k k m]
  simp only [contr, sq4, Finset.sum_add_distrib]
  rw [h1, mMat]
  ring

omit [DecidableEq ι] in
/-- The full trace `σ = S_iikk = 2x + |v|²`. -/
theorem mtrace_contr_sq4 {c : ι → ι → ι → ℝ} (hc : Symm c) :
    mtrace (contr (sq4 c)) = 2 * strength c + vinner (trVec c) (trVec c) := by
  simp only [mtrace, contr_sq4 hc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [trVec]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [hc.s13 a a m]

omit [DecidableEq ι] in
/-- `tr M² = ⟨M, M⟩`, the double-square sum. -/
theorem quadSum_eq_minner {c : ι → ι → ι → ℝ} (hc : Symm c) :
    quadSum c c c c = minner (mMat c) (mMat c) := by
  have : minner (mMat c) (mMat c) = ∑ t : Six ι,
      c t.1 t.2.2.1 t.2.2.2.2.1 * c t.2.1 t.2.2.1 t.2.2.2.2.1 *
        (c t.1 t.2.2.2.1 t.2.2.2.2.2 * c t.2.1 t.2.2.2.1 t.2.2.2.2.2) := by
    simp only [minner, mMat, Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [this]
  refine (Fintype.sum_equiv
    ⟨fun t => (t.1, t.2.2.1, t.2.2.2.2.1, t.2.1, t.2.2.2.1, t.2.2.2.2.2),
      fun t => (t.1, t.2.2.2.1, t.2.1, t.2.2.2.2.1, t.2.2.1, t.2.2.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun t => ?_).symm
  obtain ⟨i, j, x, y, z, w⟩ := t
  simp only [Equiv.coe_fn_mk, quadTerm]
  ring

/-! The quartic form. -/

omit [DecidableEq ι] in
theorem form4_pairT (c : ι → ι → ι → ℝ) (φ : ι → ℝ) :
    form4 (pairT c) φ = ∑ m, (∑ i, ∑ j, c i j m * (φ i * φ j)) ^ 2 := by
  simp only [form4, pairT, sq, Finset.sum_mul, Finset.mul_sum]
  have fl1 : ∀ f : ι → ι → ι → ι → ι → ℝ, ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, f i j k l m =
      ∑ t : ι × ι × ι × ι × ι, f t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 := by
    intro f; simp only [Fintype.sum_prod_type]
  have fl2 : ∀ f : ι → ι → ι → ι → ι → ℝ, ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l m =
      ∑ t : ι × ι × ι × ι × ι, f t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 t.1 := by
    intro f; simp only [Fintype.sum_prod_type]
  rw [fl1, fl2]
  refine Fintype.sum_equiv
    ⟨fun t => (t.2.2.2.2, t.1, t.2.1, t.2.2.1, t.2.2.2.1),
      fun t => (t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2, t.1), fun _ => rfl, fun _ => rfl⟩
    _ _ fun t => ?_
  obtain ⟨i, j, k, l, m⟩ := t
  simp only [Equiv.coe_fn_mk]
  ring

omit [DecidableEq ι] in
/-- `S(φ,φ,φ,φ) = 3 Σ_m (c_ijm φ_i φ_j)²`. -/
theorem form4_sq4 (c : ι → ι → ι → ℝ) (φ : ι → ℝ) :
    form4 (sq4 c) φ = 3 * ∑ m, (∑ i, ∑ j, c i j m * (φ i * φ j)) ^ 2 := by
  have e : form4 (sq4 c) φ = form4 (pairT c) φ + form4 (fun i j k l => pairT c i k j l) φ +
      form4 (fun i j k l => pairT c i l j k) φ := by
    simp only [form4, sq4_eq_pairT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have e2 : form4 (fun i j k l => pairT c i k j l) φ = form4 (pairT c) φ := by
    simp only [form4]; rw [sum4_swap23]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have e3 : form4 (fun i j k l => pairT c i l j k) φ = form4 (pairT c) φ := by
    simp only [form4]; rw [sum4_swap34, sum4_swap23]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e, e2, e3, form4_pairT]
  ring

end Quartic

end

end ThirteenPlanes
