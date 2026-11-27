module

public import Glennie.Native.Triality

@[expose] public section

set_option backward.privateInPublic true

/-! Octonion conjugation cannot occupy the first slot of a multiplication-related triple. -/

namespace ThirteenPlanes.AlbertTriality

open Glennie

private theorem noConjugationIntertwiner (p : Octonion)
    (h : ∀ x y, octMul (octConj x) (octMul (octConj y) p) =
      octMul (octConj (octMul x y)) p) : p = 0 := by
  let i : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let j : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  let k : Quaternion ℝ := ⟨0, 0, 0, 1⟩
  -- These three pairs lie in quaternionic subalgebras. Their equations together
  -- force both quaternion coordinate projections of the intertwiner to vanish.
  have hleft := QuaternionAlgebra.ext_iff.mp (congrArg Prod.fst (h (i, 0) (j, 0)))
  have hrealI := QuaternionAlgebra.ext_iff.mp (congrArg Prod.snd (h (0, 1) (0, i)))
  have hJK := QuaternionAlgebra.ext_iff.mp (congrArg Prod.snd (h (0, j) (0, k)))
  rcases hleft with ⟨h₁, h₂, h₃, h₄⟩
  rcases hrealI with ⟨h₅, h₆, -, -⟩
  rcases hJK with ⟨-, -, h₇, h₈⟩
  simp [octMul, octConj, i, j, k] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  apply Prod.ext
  · apply Quaternion.ext <;> simp <;> linarith
  · apply Quaternion.ext <;> simp <;> linarith

/-- The forbidden first component in Yokota's determinant-one argument. -/
theorem no_related_first_conj (g : OctRelatedTriple) : g.A ≠ octConjEquiv := by
  intro hA
  have hA' (x : Octonion) : g.A x = octConj x := by
    rw [hA]
    rfl
  have hBC (y : Octonion) : g.B y = g.C y := by
    simpa only [hA', octConj_scalar, octMul_scalar_left, one_smul]
      using g.product (octScalar 1) y
  let p := g.B (octScalar 1)
  have hform (x : Octonion) : g.B x = octMul (octConj x) p := by
    rw [hBC x]
    simpa only [hA', octMul_scalar_right, one_smul] using (g.product x (octScalar 1)).symm
  have hh (x y : Octonion) : octMul (octConj x) (octMul (octConj y) p) =
      octMul (octConj (octMul x y)) p := by
    rw [← hA', ← hform, g.product, ← hBC, hform]
  have hp : p = 0 := noConjugationIntertwiner p hh
  have hzero : octScalar 1 = 0 := g.B.injective (hp.trans (map_zero g.B).symm)
  have hr := congrArg (fun x : Octonion => x.1.re) hzero
  norm_num [octScalar] at hr

end ThirteenPlanes.AlbertTriality
