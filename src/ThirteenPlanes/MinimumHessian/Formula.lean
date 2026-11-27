module

public import ThirteenPlanes.Quartic

@[expose] public section

/-! The second variation of the A-function.

`gradPair C k` is the derivative of `A` at `C` in the direction `k` (from `aFunction_hasDerivAt`).
Its derivative along `C + s D` at `s = 0` is the Hessian bilinear form, written in orthonormal
coordinates as

  `hessC c d k = -½⟨k,d⟩ + (3/2)(Q(k,d,c,c) + Q(k,c,d,c) + Q(k,c,c,d)) + 6 P(k,d,c,c)`,

with `Q` the double-square sum and `P` the tetrahedron sum. It is symmetric in `d, k` and does not
depend on the basis. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)

/-- The first variation `dA_C[k] = -16π² ⟨k, β(C)⟩` of the A-function. -/
def gradPair (C k : SymmetricCubic V) : ℝ :=
  -(16 * Real.pi ^ 2) * k.tensorPairing (oneLoopBeta (16 * Real.pi ^ 2)⁻¹ C)

/-- The Hessian of the A-function in coordinates. -/
def hessC (c d k : ι → ι → ι → ℝ) : ℝ :=
  -(1 / 2) * cinner k d + 3 / 2 * (quadSum k d c c + quadSum k c d c + quadSum k c c d) +
    6 * tetSum k d c c

theorem gradPair_eq (C k : SymmetricCubic V) :
    gradPair C k = -(1 / 2) * cinner (k.coefficient e) (C.coefficient e) +
      3 / 2 * quadSum (k.coefficient e) (C.coefficient e) (C.coefficient e) (C.coefficient e) +
      2 * tetSum (k.coefficient e) (C.coefficient e) (C.coefficient e) (C.coefficient e) := by
  rw [gradPair, oneLoopBeta, SymmetricCubic.tensorPairing_smul_right,
    SymmetricCubic.tensorPairing_sub_right, SymmetricCubic.tensorPairing_sub_right,
    SymmetricCubic.tensorPairing_smul_right, SymmetricCubic.tensorPairing_smul_right,
    SymmetricCubic.tensorPairing_smul_right,
    SymmetricCubic.tensorPairing_insert_doubleContraction e,
    SymmetricCubic.tensorPairing_triangle_eq e, SymmetricCubic.tensorPairing_eq_sum e]
  have hπ : (16 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [cinner, SymmetricCubic.coefficient]
  field_simp
  ring

omit [Fintype ι] in
theorem hasDerivAt_sum_mul3c {T : Type*} [Fintype T] (k q r w q' r' w' : T → ℝ) :
    HasDerivAt (fun s : ℝ => ∑ t, k t * (q t + s * q' t) * (r t + s * r' t) * (w t + s * w' t))
      (∑ t, (k t * q' t * r t * w t + k t * q t * r' t * w t + k t * q t * r t * w' t)) 0 := by
  refine HasDerivAt.fun_sum fun t _ => ?_
  exact ((((hasDerivAt_const (0 : ℝ) (k t)).mul (hasDerivAt_affine _ _)).mul
    (hasDerivAt_affine _ _)).mul (hasDerivAt_affine _ _)).congr_deriv (by simp; ring)

theorem cinner_path (k c d : ι → ι → ι → ℝ) (s : ℝ) :
    cinner k (path c d s) = cinner k c + s * cinner k d := by
  simp only [cinner, path, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem hasDerivAt_quadSum_k (k c d : ι → ι → ι → ℝ) :
    HasDerivAt (fun s => quadSum k (path c d s) (path c d s) (path c d s))
      (quadSum k d c c + quadSum k c d c + quadSum k c c d) 0 := by
  have := hasDerivAt_sum_mul3c (T := Six ι) (fun t => k t.1 t.2.1 t.2.2.1)
    (fun t => c t.2.2.2.1 t.2.1 t.2.2.1) (fun t => c t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun t => c t.1 t.2.2.2.2.1 t.2.2.2.2.2) (fun t => d t.2.2.2.1 t.2.1 t.2.2.1)
    (fun t => d t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2) (fun t => d t.1 t.2.2.2.2.1 t.2.2.2.2.2)
  refine this.congr_deriv ?_
  simp only [quadSum, quadTerm, ← Finset.sum_add_distrib]

theorem hasDerivAt_tetSum_k {k c d : ι → ι → ι → ℝ} (hk : Symm k) (hc : Symm c) (hd : Symm d) :
    HasDerivAt (fun s => tetSum k (path c d s) (path c d s) (path c d s))
      (3 * tetSum k d c c) 0 := by
  have := hasDerivAt_sum_mul3c (T := Six ι) (fun t => k t.1 t.2.1 t.2.2.1)
    (fun t => c t.1 t.2.2.2.1 t.2.2.2.2.1) (fun t => c t.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun t => c t.2.2.1 t.2.2.2.2.2 t.2.2.2.1) (fun t => d t.1 t.2.2.2.1 t.2.2.2.2.1)
    (fun t => d t.2.1 t.2.2.2.2.1 t.2.2.2.2.2) (fun t => d t.2.2.1 t.2.2.2.2.2 t.2.2.2.1)
  refine this.congr_deriv ?_
  have e1 : tetSum k c d c = tetSum k d c c :=
    (tetSum_swap12 hc hk hd hc).trans ((tetSum_swap13 hd hk hc hc).trans
      (tetSum_swap12 hd hk hc hc).symm)
  have e2 : tetSum k c c d = tetSum k d c c :=
    (tetSum_swap12 hc hk hc hd).trans ((tetSum_swap14 hd hk hc hc).trans
      (tetSum_swap12 hd hk hc hc).symm)
  have : ∑ t : Six ι, (k t.1 t.2.1 t.2.2.1 * d t.1 t.2.2.2.1 t.2.2.2.2.1 *
      c t.2.1 t.2.2.2.2.1 t.2.2.2.2.2 * c t.2.2.1 t.2.2.2.2.2 t.2.2.2.1 +
      k t.1 t.2.1 t.2.2.1 * c t.1 t.2.2.2.1 t.2.2.2.2.1 * d t.2.1 t.2.2.2.2.1 t.2.2.2.2.2 *
      c t.2.2.1 t.2.2.2.2.2 t.2.2.2.1 +
      k t.1 t.2.1 t.2.2.1 * c t.1 t.2.2.2.1 t.2.2.2.2.1 * c t.2.1 t.2.2.2.2.1 t.2.2.2.2.2 *
      d t.2.2.1 t.2.2.2.2.2 t.2.2.2.1) = tetSum k d c c + tetSum k c d c + tetSum k c c d := by
    simp only [tetSum, tetTerm, ← Finset.sum_add_distrib]
  rw [this, e1, e2]; ring

/-- The Hessian is the derivative of the first variation: `d/ds dA_{C+sD}[k] = hessC c d k`. -/
theorem hasDerivAt_gradPair (C D k : SymmetricCubic V) :
    HasDerivAt (fun s : ℝ => gradPair (C + s • D) k)
      (hessC (C.coefficient e) (D.coefficient e) (k.coefficient e)) 0 := by
  have hf : (fun s : ℝ => gradPair (C + s • D) k) = fun s =>
      -(1 / 2) * (cinner (k.coefficient e) (C.coefficient e) +
        s * cinner (k.coefficient e) (D.coefficient e)) +
      3 / 2 * quadSum (k.coefficient e) (path (C.coefficient e) (D.coefficient e) s)
        (path (C.coefficient e) (D.coefficient e) s) (path (C.coefficient e) (D.coefficient e) s) +
      2 * tetSum (k.coefficient e) (path (C.coefficient e) (D.coefficient e) s)
        (path (C.coefficient e) (D.coefficient e) s) (path (C.coefficient e) (D.coefficient e) s) := by
    funext s
    rw [gradPair_eq e, SymmetricCubic.coefficient_path e, cinner_path]
  rw [hf]
  have := ((((hasDerivAt_affine (cinner (k.coefficient e) (C.coefficient e))
    (cinner (k.coefficient e) (D.coefficient e))).const_mul (-(1 / 2))).add
    ((hasDerivAt_quadSum_k (k.coefficient e) (C.coefficient e) (D.coefficient e)).const_mul
      (3 / 2))).add
    ((hasDerivAt_tetSum_k (SymmetricCubic.coefficient_symm e k)
      (SymmetricCubic.coefficient_symm e C) (SymmetricCubic.coefficient_symm e D)).const_mul 2))
  refine this.congr_deriv ?_
  simp only [hessC]
  ring

/-- The Hessian bilinear form of the A-function at `C`, evaluated on `D` and `k`. -/
def aHessian (C D k : SymmetricCubic V) : ℝ :=
  hessC ((C.coefficient (stdOrthonormalBasis ℝ V))) (D.coefficient (stdOrthonormalBasis ℝ V))
    (k.coefficient (stdOrthonormalBasis ℝ V))

/-- The Hessian in any orthonormal basis. -/
theorem aHessian_eq (C D k : SymmetricCubic V) :
    aHessian C D k = hessC (C.coefficient e) (D.coefficient e) (k.coefficient e) :=
  (hasDerivAt_gradPair (stdOrthonormalBasis ℝ V) C D k).unique (hasDerivAt_gradPair e C D k)

/-- `aHessian C D k` is the derivative at `s = 0` of the first variation `dA_{C+sD}[k]`. -/
theorem hasDerivAt_gradPair_aHessian (C D k : SymmetricCubic V) :
    HasDerivAt (fun s : ℝ => gradPair (C + s • D) k) (aHessian C D k) 0 :=
  hasDerivAt_gradPair _ C D k

/-- The first variation is the derivative of `A` along lines. -/
theorem hasDerivAt_aFunction_line (C D : SymmetricCubic V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => aFunction (C + t • D)) (gradPair (C + s • D) D) s := by
  have h0 := aFunction_hasDerivAt (C + s • D) D
  have h1 : HasDerivAt (fun t : ℝ => aFunction (C + s • D + (t - s) • D)) (gradPair (C + s • D) D) s := by
    have h0' : HasDerivAt (fun r : ℝ => aFunction (C + s • D + r • D))
        (gradPair (C + s • D) D) (s - s) := by rw [sub_self]; exact h0
    exact HasDerivAt.comp_sub_const s s h0'
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only
  congr 1
  apply SymmetricCubic.ext; intro x y z
  simp only [SymmetricCubic.apply_add, SymmetricCubic.apply_smul]; ring

/-- **Second derivative along lines.** The derivative of `t ↦ A(C + tD)` has derivative
`aHessian C D D` at `0`. -/
theorem hasDerivAt_deriv_aFunction_line (C D : SymmetricCubic V) :
    HasDerivAt (deriv fun t : ℝ => aFunction (C + t • D)) (aHessian C D D) 0 := by
  have : deriv (fun t : ℝ => aFunction (C + t • D)) = fun s => gradPair (C + s • D) D :=
    funext fun s => (hasDerivAt_aFunction_line C D s).deriv
  rw [this]
  exact hasDerivAt_gradPair_aHessian C D D

theorem hessC_comm {c d k : ι → ι → ι → ℝ} (hc : Symm c) (hd : Symm d) (hk : Symm k) :
    hessC c d k = hessC c k d := by
  simp only [hessC]
  rw [show cinner k d = cinner d k by simp only [cinner, mul_comm],
    ← quadSum_swap_ab_cd k d c c, ← quadSum_swap_ac_bd k c d c, ← quadSum_swap_ad_bc k c c d,
    tetSum_swap12 hd hk hc hc]

/-- The Hessian form is symmetric. -/
theorem aHessian_comm (C D k : SymmetricCubic V) : aHessian C D k = aHessian C k D := by
  simp only [aHessian]
  exact hessC_comm (SymmetricCubic.coefficient_symm _ C) (SymmetricCubic.coefficient_symm _ D)
    (SymmetricCubic.coefficient_symm _ k)

end

end ThirteenPlanes
