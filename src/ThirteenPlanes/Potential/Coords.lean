module

public import ThirteenPlanes.Cubic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

set_option backward.privateInPublic true

/-! Coordinate sums for the quartic contractions of cubics.

Two six-index sums of four coefficient arrays: the tetrahedron, in which every pair of the four
arrays shares one index, and the double square, a four-cycle whose edges alternate between two
shared indices and one. Their permutation symmetries and the derivative of a product of four affine
arrays are what the gradient computation in `ThirteenPlanes.Potential` uses. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Coords

variable {ι : Type*} [Fintype ι]

/-- Six indices. -/
abbrev Six (ι : Type*) := ι × ι × ι × ι × ι × ι

/-- The tetrahedron term `a_ijk b_ixy c_jyz d_kzx` at `(i,j,k,x,y,z)`. -/
def tetTerm (a b c d : ι → ι → ι → ℝ) (t : Six ι) : ℝ :=
  a t.1 t.2.1 t.2.2.1 * b t.1 t.2.2.2.1 t.2.2.2.2.1 * c t.2.1 t.2.2.2.2.1 t.2.2.2.2.2 *
    d t.2.2.1 t.2.2.2.2.2 t.2.2.2.1

/-- The tetrahedron sum of four coefficient arrays. -/
def tetSum (a b c d : ι → ι → ι → ℝ) : ℝ := ∑ t : Six ι, tetTerm a b c d t

/-- The double-square term `a_ixy b_jxy c_jzw d_izw` at `(i,x,y,j,z,w)`. -/
def quadTerm (a b c d : ι → ι → ι → ℝ) (t : Six ι) : ℝ :=
  a t.1 t.2.1 t.2.2.1 * b t.2.2.2.1 t.2.1 t.2.2.1 * c t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 *
    d t.1 t.2.2.2.2.1 t.2.2.2.2.2

/-- The double-square sum of four coefficient arrays. -/
def quadSum (a b c d : ι → ι → ι → ℝ) : ℝ := ∑ t : Six ι, quadTerm a b c d t

/-- A fully symmetric coefficient array. -/
structure Symm (a : ι → ι → ι → ℝ) : Prop where
  s12 : ∀ i j k, a i j k = a j i k
  s23 : ∀ i j k, a i j k = a i k j

omit [Fintype ι] in
theorem Symm.s13 {a : ι → ι → ι → ℝ} (ha : Symm a) (i j k : ι) : a i j k = a k j i := by
  rw [ha.s12, ha.s23, ha.s12]

private def perm (f : Six ι → Six ι) (hf : Function.Involutive f) : Six ι ≃ Six ι :=
  ⟨f, f, hf.leftInverse, hf.rightInverse⟩

theorem tetSum_swap12 {a b c d : ι → ι → ι → ℝ} (ha : Symm a) (hb : Symm b) (hc : Symm c)
    (hd : Symm d) : tetSum b a c d = tetSum a b c d := by
  refine Fintype.sum_equiv (perm (fun t => (t.1, t.2.2.2.2.1, t.2.2.2.1, t.2.2.1, t.2.1, t.2.2.2.2.2))
    (fun _ => rfl)) _ _ fun t => ?_
  obtain ⟨i, j, k, x, y, z⟩ := t
  simp only [perm, Equiv.coe_fn_mk, tetTerm]
  rw [ha.s23 i x y, hb.s23 i j k, hc.s12 j y z, hd.s13 k z x]
  ring

theorem tetSum_swap13 {a b c d : ι → ι → ι → ℝ} (ha : Symm a) (hb : Symm b) (hc : Symm c)
    (hd : Symm d) : tetSum c b a d = tetSum a b c d := by
  refine Fintype.sum_equiv (perm (fun t => (t.2.2.2.2.1, t.2.1, t.2.2.2.2.2, t.2.2.2.1, t.1, t.2.2.1))
    (fun _ => rfl)) _ _ fun t => ?_
  obtain ⟨i, j, k, x, y, z⟩ := t
  simp only [perm, Equiv.coe_fn_mk, tetTerm]
  rw [ha.s12 j y z, hb.s13 i x y, hc.s12 i j k, hd.s12 k z x]
  ring

theorem tetSum_swap14 {a b c d : ι → ι → ι → ℝ} (ha : Symm a) (hb : Symm b) (hc : Symm c)
    (hd : Symm d) : tetSum d b c a = tetSum a b c d := by
  refine Fintype.sum_equiv (perm (fun t => (t.2.2.2.1, t.2.2.2.2.2, t.2.2.1, t.1, t.2.2.2.2.1, t.2.1))
    (fun _ => rfl)) _ _ fun t => ?_
  obtain ⟨i, j, k, x, y, z⟩ := t
  simp only [perm, Equiv.coe_fn_mk, tetTerm]
  rw [ha.s13 k z x, hb.s12 i x y, hc.s13 j y z, hd.s13 i j k]
  ring

theorem quadSum_swap_ab_cd (a b c d : ι → ι → ι → ℝ) : quadSum b a d c = quadSum a b c d := by
  refine Fintype.sum_equiv (perm (fun t => (t.2.2.2.1, t.2.1, t.2.2.1, t.1, t.2.2.2.2.1, t.2.2.2.2.2))
    (fun _ => rfl)) _ _ fun t => ?_
  obtain ⟨i, x, y, j, z, w⟩ := t
  simp only [perm, Equiv.coe_fn_mk, quadTerm]
  ring

theorem quadSum_swap_ac_bd (a b c d : ι → ι → ι → ℝ) : quadSum c d a b = quadSum a b c d := by
  refine Fintype.sum_equiv (perm (fun t => (t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2, t.1, t.2.1, t.2.2.1))
    (fun _ => rfl)) _ _ fun t => ?_
  obtain ⟨i, x, y, j, z, w⟩ := t
  simp only [perm, Equiv.coe_fn_mk, quadTerm]
  ring

theorem quadSum_swap_ad_bc (a b c d : ι → ι → ι → ℝ) : quadSum d c b a = quadSum a b c d := by
  refine Fintype.sum_equiv (perm (fun t => (t.1, t.2.2.2.2.1, t.2.2.2.2.2, t.2.2.2.1, t.2.1, t.2.2.1))
    (fun _ => rfl)) _ _ fun t => ?_
  obtain ⟨i, x, y, j, z, w⟩ := t
  simp only [perm, Equiv.coe_fn_mk, quadTerm]
  ring

theorem hasDerivAt_affine (p p' : ℝ) : HasDerivAt (fun s : ℝ => p + s * p') p' 0 :=
  ((hasDerivAt_id' (0 : ℝ)).mul_const p').const_add p |>.congr_deriv (by simp)

/-- Derivative at zero of a sum of products of two affine functions. -/
theorem hasDerivAt_sum_mul2 {T : Type*} [Fintype T] (p q p' q' : T → ℝ) :
    HasDerivAt (fun s : ℝ => ∑ t, (p t + s * p' t) * (q t + s * q' t))
      (∑ t, (p' t * q t + p t * q' t)) 0 := by
  refine HasDerivAt.fun_sum fun t _ => ?_
  exact ((hasDerivAt_affine _ _).mul (hasDerivAt_affine _ _)).congr_deriv (by simp)

/-- Derivative at zero of a sum of products of four affine functions. -/
theorem hasDerivAt_sum_mul4 {T : Type*} [Fintype T] (p q r w p' q' r' w' : T → ℝ) :
    HasDerivAt (fun s : ℝ => ∑ t, (p t + s * p' t) * (q t + s * q' t) * (r t + s * r' t) *
        (w t + s * w' t))
      (∑ t, (p' t * q t * r t * w t + p t * q' t * r t * w t + p t * q t * r' t * w t +
        p t * q t * r t * w' t)) 0 := by
  refine HasDerivAt.fun_sum fun t _ => ?_
  exact ((((hasDerivAt_affine _ _).mul (hasDerivAt_affine _ _)).mul (hasDerivAt_affine _ _)).mul
    (hasDerivAt_affine _ _)).congr_deriv (by simp; ring)

/-- The affine path of arrays. -/
def path (a a' : ι → ι → ι → ℝ) (s : ℝ) : ι → ι → ι → ℝ := fun i j k => a i j k + s * a' i j k

theorem hasDerivAt_tetSum_path (a a' : ι → ι → ι → ℝ) :
    HasDerivAt (fun s => tetSum (path a a' s) (path a a' s) (path a a' s) (path a a' s))
      (tetSum a' a a a + tetSum a a' a a + tetSum a a a' a + tetSum a a a a') 0 := by
  have := hasDerivAt_sum_mul4 (T := Six ι) (fun t => a t.1 t.2.1 t.2.2.1)
    (fun t => a t.1 t.2.2.2.1 t.2.2.2.2.1) (fun t => a t.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun t => a t.2.2.1 t.2.2.2.2.2 t.2.2.2.1) (fun t => a' t.1 t.2.1 t.2.2.1)
    (fun t => a' t.1 t.2.2.2.1 t.2.2.2.2.1) (fun t => a' t.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun t => a' t.2.2.1 t.2.2.2.2.2 t.2.2.2.1)
  refine this.congr_deriv ?_
  simp only [tetSum, tetTerm, ← Finset.sum_add_distrib]

theorem hasDerivAt_quadSum_path (a a' : ι → ι → ι → ℝ) :
    HasDerivAt (fun s => quadSum (path a a' s) (path a a' s) (path a a' s) (path a a' s))
      (quadSum a' a a a + quadSum a a' a a + quadSum a a a' a + quadSum a a a a') 0 := by
  have := hasDerivAt_sum_mul4 (T := Six ι) (fun t => a t.1 t.2.1 t.2.2.1)
    (fun t => a t.2.2.2.1 t.2.1 t.2.2.1) (fun t => a t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun t => a t.1 t.2.2.2.2.1 t.2.2.2.2.2) (fun t => a' t.1 t.2.1 t.2.2.1)
    (fun t => a' t.2.2.2.1 t.2.1 t.2.2.1) (fun t => a' t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun t => a' t.1 t.2.2.2.2.1 t.2.2.2.2.2)
  refine this.congr_deriv ?_
  simp only [quadSum, quadTerm, ← Finset.sum_add_distrib]

/-- The derivative of the tetrahedron sum along a path of symmetric arrays. -/
theorem hasDerivAt_tetSum_path_symm {a a' : ι → ι → ι → ℝ} (ha : Symm a) (ha' : Symm a') :
    HasDerivAt (fun s => tetSum (path a a' s) (path a a' s) (path a a' s) (path a a' s))
      (4 * tetSum a' a a a) 0 := by
  refine (hasDerivAt_tetSum_path a a').congr_deriv ?_
  rw [tetSum_swap12 ha' ha ha ha, tetSum_swap13 ha' ha ha ha, tetSum_swap14 ha' ha ha ha]
  ring

/-- The derivative of the double-square sum along a path of arrays. -/
theorem hasDerivAt_quadSum_path' (a a' : ι → ι → ι → ℝ) :
    HasDerivAt (fun s => quadSum (path a a' s) (path a a' s) (path a a' s) (path a a' s))
      (4 * quadSum a' a a a) 0 := by
  refine (hasDerivAt_quadSum_path a a').congr_deriv ?_
  rw [quadSum_swap_ab_cd a' a a a, quadSum_swap_ac_bd a' a a a, quadSum_swap_ad_bc a' a a a]
  ring

end Coords

end

end ThirteenPlanes
