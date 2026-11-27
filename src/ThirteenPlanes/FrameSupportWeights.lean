/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FrameSupportProduct

@[expose] public section

set_option backward.privateInPublic true

/-! The weights of the native frame triples from Appendix support bound from pairwise unbiasedness. -/

noncomputable section

namespace ThirteenPlanes

open scoped BigOperators

def TightNativeCode.frameBasis (c : TightNativeCode) (f : Fin 13) :
    OrthonormalBasis (Fin 2) ℝ (c.decomposition.plane f) :=
  (stdOrthonormalBasis ℝ (c.decomposition.plane f)).reindex
    (finCongr (c.decomposition.dimension f))

def TightNativeCode.frameVector (c : TightNativeCode) (f : Fin 13) (i : Fin 2) :
    NativeTraceless := c.frameBasis f i

@[simp] theorem TightNativeCode.frameVector_mem (c : TightNativeCode) (f : Fin 13) (i : Fin 2) :
    c.frameVector f i ∈ c.decomposition.plane f := (c.frameBasis f i).property

theorem TightNativeCode.frameVector_inner (c : TightNativeCode) (f : Fin 13) (i j : Fin 2) :
    inner ℝ (c.frameVector f i) (c.frameVector f j) = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (c.frameBasis f).orthonormal i j

theorem TightNativeCode.frameVector_norm_sq (c : TightNativeCode) (f : Fin 13) (i : Fin 2) :
    ‖c.frameVector f i‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, c.frameVector_inner, ite_eq_left rfl]

def TightNativeCode.crossVector (c : TightNativeCode) (f g : Fin 13) (a : Fin 2 × Fin 2) :
    NativeTraceless :=
  nativeCenteredJordan (c.frameVector f a.1) (c.frameVector g a.2)

theorem TightNativeCode.crossVector_inner (c : TightNativeCode) {f g : Fin 13} (hfg : f ≠ g)
    (a b : Fin 2 × Fin 2) :
    inner ℝ (c.crossVector f g a) (c.crossVector f g b) = if a = b then 1 / 12 else 0 := by
  change inner ℝ (nativeCenteredJordan (c.frameBasis f a.1) (c.frameBasis g a.2))
    (nativeCenteredJordan (c.frameBasis f b.1) (c.frameBasis g b.2)) = _
  rw [c.crossProduct_inner hfg]
  change inner ℝ (c.frameVector f a.1) (c.frameVector f b.1) *
    inner ℝ (c.frameVector g a.2) (c.frameVector g b.2) / 12 = _
  rw [c.frameVector_inner, c.frameVector_inner]
  by_cases h₁ : a.1 = b.1 <;> by_cases h₂ : a.2 = b.2 <;> simp [Prod.ext_iff, h₁, h₂]

theorem TightNativeCode.scaledCrossVector_orthonormal (c : TightNativeCode) {f g : Fin 13} (hfg : f ≠ g) :
    Orthonormal ℝ (fun a : Fin 2 × Fin 2 => Real.sqrt 12 • c.crossVector f g a) := by
  rw [orthonormal_iff_ite]
  intro a b
  have hs : Real.sqrt 12 * Real.sqrt 12 = (12 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  rw [real_inner_smul_left (c.crossVector f g a), real_inner_smul_right (c.crossVector f g a),
    ← mul_assoc, hs, c.crossVector_inner hfg]
  split_ifs <;> norm_num

/-- Six times the squared tensor norm of the native equal-strength cubic on three planes. -/
def TightNativeCode.frameWeight (c : TightNativeCode) (f g h : Fin 13) : ℝ :=
  6 * ∑ i : Fin 2, ∑ a : Fin 2 × Fin 2,
    (inner ℝ (c.crossVector f g a) (c.frameVector h i)) ^ 2

theorem TightNativeCode.frameWeight_nonneg (c : TightNativeCode) (f g h : Fin 13) :
    0 ≤ c.frameWeight f g h := by
  unfold frameWeight
  positivity

theorem TightNativeCode.frameWeight_le_one (c : TightNativeCode) {f g : Fin 13}
    (hfg : f ≠ g) (h : Fin 13) : c.frameWeight f g h ≤ 1 := by
  have hrow (i : Fin 2) : ∑ a : Fin 2 × Fin 2,
      (inner ℝ (c.crossVector f g a) (c.frameVector h i)) ^ 2 ≤ 1 / 12 := by
    have hb := (c.scaledCrossVector_orthonormal hfg).sum_inner_products_le (c.frameVector h i)
      (s := Finset.univ)
    have hterm (a : Fin 2 × Fin 2) :
        (inner ℝ (Real.sqrt 12 • c.crossVector f g a) (c.frameVector h i)) ^ 2 =
          12 * (inner ℝ (c.crossVector f g a) (c.frameVector h i)) ^ 2 := by
      rw [real_inner_smul_left (c.crossVector f g a), mul_pow, Real.sq_sqrt (by norm_num)]
    simp only [Real.norm_eq_abs, sq_abs, hterm, ← Finset.mul_sum, c.frameVector_norm_sq] at hb
    linarith
  have hb : (∑ i : Fin 2, ∑ a : Fin 2 × Fin 2,
      (inner ℝ (c.crossVector f g a) (c.frameVector h i)) ^ 2) ≤ 1 / 6 := by
    calc
      _ ≤ ∑ _i : Fin 2, (1 / 12 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by norm_num
  unfold frameWeight
  linarith

theorem TightNativeCode.crossVector_orthogonal_left (c : TightNativeCode) {f g : Fin 13}
    (hfg : f ≠ g) (a : Fin 2 × Fin 2) (z : NativeTraceless) (hz : z ∈ c.decomposition.plane f) :
    inner ℝ (c.crossVector f g a) z = 0 := by
  unfold crossVector
  rw [nativeCenterJordan_inner_swap]
  exact (c.planes_orthogonal hfg).inner_eq
    (nativeFramePlane_closed (c.frame f) (c.frameVector_mem f a.1) hz)
    (c.frameVector_mem g a.2)

theorem TightNativeCode.crossVector_orthogonal_right (c : TightNativeCode) {f g : Fin 13}
    (hfg : f ≠ g) (a : Fin 2 × Fin 2) (z : NativeTraceless) (hz : z ∈ c.decomposition.plane g) :
    inner ℝ (c.crossVector f g a) z = 0 := by
  have hs : c.crossVector f g a = c.crossVector g f (a.2, a.1) :=
    nativeCenterJordan_comm _ _
  rw [hs]
  exact c.crossVector_orthogonal_left hfg.symm (a.2, a.1) z hz

theorem TightNativeCode.frameWeight_repeated_left (c : TightNativeCode) {f g : Fin 13} (hfg : f ≠ g) :
    c.frameWeight f g f = 0 := by
  have h (i : Fin 2) (a : Fin 2 × Fin 2) :
      inner ℝ (c.crossVector f g a) (c.frameVector f i) = 0 :=
    c.crossVector_orthogonal_left hfg a _ (c.frameVector_mem _ _)
  simp only [frameWeight, h, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero]

theorem TightNativeCode.frameWeight_repeated_right (c : TightNativeCode) {f g : Fin 13} (hfg : f ≠ g) :
    c.frameWeight f g g = 0 := by
  have h (i : Fin 2) (a : Fin 2 × Fin 2) :
      inner ℝ (c.crossVector f g a) (c.frameVector g i) = 0 :=
    c.crossVector_orthogonal_right hfg a _ (c.frameVector_mem _ _)
  simp only [frameWeight, h, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero]

private theorem frameVectors_orthonormal (c : TightNativeCode) :
    Orthonormal ℝ (fun a : Fin 13 × Fin 2 => c.frameVector a.1 a.2) := by
  rw [orthonormal_iff_ite]
  rintro ⟨f, i⟩ ⟨g, j⟩
  by_cases hfg : f = g
  · subst g
    simpa [Prod.ext_iff] using c.frameVector_inner f i j
  · simpa [Prod.ext_iff, hfg] using
      (c.planes_orthogonal hfg).inner_eq (c.frameVector_mem f i) (c.frameVector_mem g j)

private def frameVectors_basis (c : TightNativeCode) :
    OrthonormalBasis (Fin 13 × Fin 2) ℝ NativeTraceless := by
  refine OrthonormalBasis.mk (frameVectors_orthonormal c) ?_
  apply le_of_eq
  symm
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card (frameVectors_orthonormal c).linearIndependent,
    nativeTraceless_finrank]
  simp

theorem TightNativeCode.frameWeight_pair_sum (c : TightNativeCode) {f g : Fin 13} (hfg : f ≠ g) :
    (∑ h : Fin 13, c.frameWeight f g h) = 2 := by
  unfold frameWeight
  rw [← Finset.mul_sum]
  have hsum : (∑ h : Fin 13, ∑ i : Fin 2, ∑ a : Fin 2 × Fin 2,
      (inner ℝ (c.crossVector f g a) (c.frameVector h i)) ^ 2) =
      ∑ a : Fin 2 × Fin 2, ‖c.crossVector f g a‖ ^ 2 := by
    calc
      _ = ∑ p : Fin 13 × Fin 2, ∑ a : Fin 2 × Fin 2,
          (inner ℝ (c.crossVector f g a) (c.frameVector p.1 p.2)) ^ 2 := by
        rw [Fintype.sum_prod_type]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        simpa [frameVectors_basis] using (frameVectors_basis c).sum_sq_inner_left (c.crossVector f g a)
  rw [hsum]
  have hnorm (a : Fin 2 × Fin 2) : ‖c.crossVector f g a‖ ^ 2 = 1 / 12 := by
    rw [← real_inner_self_eq_norm_sq, c.crossVector_inner hfg, ite_eq_left rfl]
  simp only [hnorm, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The fixed pair has total weight two over the other eleven frames. -/
theorem TightNativeCode.frameWeight_pair_sum_distinct (c : TightNativeCode) {f g : Fin 13}
    (hfg : f ≠ g) :
    (∑ h ∈ Finset.univ.filter (fun h : Fin 13 => h ≠ f ∧ h ≠ g), c.frameWeight f g h) = 2 := by
  rw [Finset.sum_filter, ← c.frameWeight_pair_sum hfg]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hf : h = f
  · subst h
    simp [c.frameWeight_repeated_left hfg]
  · by_cases hg : h = g
    · subst h
      simp [c.frameWeight_repeated_right hfg]
    · simp [hf, hg]

end ThirteenPlanes
