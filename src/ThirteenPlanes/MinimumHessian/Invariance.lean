module

public import ThirteenPlanes.MinimumHessian.Formula
public import ThirteenPlanes.MinimumHessian.InvCoords

@[expose] public section

/-! Infinitesimal rotation invariance of the A-function.

For a skew-adjoint `A`, the first variation of `A` at `C` in the direction of the infinitesimal
rotation `C.insert A` vanishes, for every cubic `C`. Differentiating this identity along `C + sD`
at a critical point gives `Hess_C(D, C.insert A) = 0`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)

/-- The matrix `B_ai = ⟪e a, B (e i)⟫` of an endomorphism. -/
def matOf (B : V →ₗ[ℝ] V) (a i : ι) : ℝ := ⟪e a, B (e i)⟫

/-- A skew-adjoint endomorphism. -/
def IsSkew (A : V →ₗ[ℝ] V) : Prop := ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫

namespace SymmetricCubic

theorem apply_map₁ (h : SymmetricCubic V) (B : V →ₗ[ℝ] V) (i : ι) (w u : V) :
    h.apply (B (e i)) w u = ∑ b, matOf e B b i * h.apply (e b) w u := by
  conv_lhs => rw [← e.sum_repr' (B (e i))]
  exact apply_sum₁ e h _ w u

theorem coefficient_insert (h : SymmetricCubic V) (B : V →ₗ[ℝ] V) (i x y : ι) :
    (h.insert B).coefficient e i x y = insArr (matOf e B) (h.coefficient e) i x y := by
  simp only [coefficient, apply_insert, insArr, Finset.sum_add_distrib]
  rw [h.apply_swap₁₂ (e i) (B (e x)), h.apply_swap₂₃ (e i) (e x) (B (e y)),
    h.apply_swap₁₂ (e i) (B (e y)), apply_map₁, apply_map₁, apply_map₁]
  congr 1; congr 1
  · exact Finset.sum_congr rfl fun d _ => by rw [h.apply_swap₁₂ (e d)]
  · exact Finset.sum_congr rfl fun d _ => by rw [h.apply_swap₁₂ (e d), h.apply_swap₂₃ (e i) (e d)]

theorem matOf_doubleContraction (h : SymmetricCubic V) (a i : ι) :
    matOf e h.doubleContraction a i = mMat (h.coefficient e) a i := by
  rw [matOf, real_inner_comm, inner_doubleContraction_eq_sum e, mMat_symm]
  rfl

theorem coefficient_triangle (h : SymmetricCubic V) (i x y : ι) :
    h.triangleContraction.coefficient e i x y = triArr (h.coefficient e) i x y := by
  rw [coefficient, apply_triangleContraction_eq_sum e]; rfl

theorem tensorPairing_add_left (k g h : SymmetricCubic V) :
    (g + h).tensorPairing k = g.tensorPairing k + h.tensorPairing k := by
  rw [tensorPairing_comm, tensorPairing_add_right, tensorPairing_comm k, tensorPairing_comm k]

theorem tensorPairing_smul_left (k g : SymmetricCubic V) (a : ℝ) :
    (a • g).tensorPairing k = a * g.tensorPairing k := by
  rw [tensorPairing_comm, tensorPairing_smul_right, tensorPairing_comm k]

theorem insert_add_smul (C D : SymmetricCubic V) (s : ℝ) (A : V →ₗ[ℝ] V) :
    (C + s • D).insert A = C.insert A + s • D.insert A := by
  apply ext; intro x y z
  simp only [apply_insert, apply_add, apply_smul]; ring

end SymmetricCubic

open SymmetricCubic

/-- The gradient of the A-function as a cubic, `G(C) = -½C + ½ ins_C M_C + 2T(C)`. -/
def aGrad (C : SymmetricCubic V) : SymmetricCubic V :=
  (-(1 / 2) : ℝ) • C + (1 / 2 : ℝ) • C.insert C.doubleContraction + (2 : ℝ) • C.triangleContraction

theorem gradPair_eq_aGrad (C k : SymmetricCubic V) : gradPair C k = k.tensorPairing (aGrad C) := by
  rw [gradPair, oneLoopBeta, aGrad, tensorPairing_smul_right, tensorPairing_sub_right,
    tensorPairing_sub_right, tensorPairing_smul_right, tensorPairing_smul_right,
    tensorPairing_smul_right, tensorPairing_add_right, tensorPairing_add_right,
    tensorPairing_smul_right, tensorPairing_smul_right, tensorPairing_smul_right]
  have hπ : (16 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem gradPair_add_smul (C k₁ k₂ : SymmetricCubic V) (s : ℝ) :
    gradPair C (k₁ + s • k₂) = gradPair C k₁ + s * gradPair C k₂ := by
  simp only [gradPair_eq_aGrad, tensorPairing_add_left, tensorPairing_smul_left]

theorem matOf_skew {A : V →ₗ[ℝ] V} (hA : IsSkew A) (b i : ι) :
    matOf e A b i = -matOf e A i b := by
  rw [matOf, matOf, real_inner_comm, hA]

/-- **Infinitesimal invariance.** For skew-adjoint `A`, `dA_C[C.insert A] = 0` for every cubic `C`. -/
theorem gradPair_insert_skew (C : SymmetricCubic V) {A : V →ₗ[ℝ] V} (hA : IsSkew A) :
    gradPair C (C.insert A) = 0 := by
  let e := stdOrthonormalBasis ℝ V
  set c := C.coefficient e
  have hc : Coords.Symm c := coefficient_symm e C
  rw [gradPair_eq_aGrad, tensorPairing_comm, tensorPairing_insert e]
  have hG : ∀ i x y, (aGrad C).apply (e i) (e x) (e y) =
      -(1 / 2) * c i x y + 1 / 2 * insArr (mMat c) c i x y + 2 * triArr c i x y := by
    intro i x y
    have h1 : (C.insert C.doubleContraction).coefficient e i x y =
        insArr (matOf e C.doubleContraction) c i x y :=
      SymmetricCubic.coefficient_insert e C C.doubleContraction i x y
    have h2 : C.triangleContraction.coefficient e i x y = triArr c i x y :=
      SymmetricCubic.coefficient_triangle e C i x y
    have hm : matOf e C.doubleContraction = mMat c :=
      funext fun a => funext fun i => matOf_doubleContraction e C a i
    rw [hm] at h1
    simp only [coefficient] at h1 h2
    simp only [aGrad, apply_add, apply_smul, h1, h2]; rfl
  have hA' : ∀ i x y, C.apply (A (e i)) (e x) (e y) = ∑ b, matOf e A b i * c b x y :=
    fun i x y => apply_map₁ e C A i (e x) (e y)
  simp only [coefficient, hG, hA']
  have hre : ∀ i, ∑ x, ∑ y, (-(1 / 2) * c i x y + 1 / 2 * insArr (mMat c) c i x y +
      2 * triArr c i x y) * ∑ b, matOf e A b i * c b x y =
      ∑ b, matOf e A b i * (-(1 / 2) * nMat c c i b + 1 / 2 * nMat (insArr (mMat c) c) c i b +
        2 * nMat (triArr c) c i b) := by
    intro i
    simp only [Finset.mul_sum]
    rw [sum3_rot, sum3_rot]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [nMat, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [Finset.sum_congr rfl fun i _ => hre i]
  rw [skew_sum_zero (matOf_skew e hA) fun i b => by
    rw [nMat_self_symm, nMat_ins_symm hc, nMat_tri_symm hc]]
  ring

/-- At a critical point, the Hessian vanishes against every infinitesimal rotation of the point. -/
theorem aHessian_insert_of_critical (C D : SymmetricCubic V) (hcrit : ∀ k, gradPair C k = 0)
    {A : V →ₗ[ℝ] V} (hA : IsSkew A) : aHessian C D (C.insert A) = 0 := by
  have hΦ : (fun s : ℝ => gradPair (C + s • D) ((C + s • D).insert A)) = fun _ => 0 :=
    funext fun s => gradPair_insert_skew _ hA
  have hsplit : (fun s : ℝ => gradPair (C + s • D) ((C + s • D).insert A)) = fun s =>
      gradPair (C + s • D) (C.insert A) + s * gradPair (C + s • D) (D.insert A) :=
    funext fun s => by rw [insert_add_smul, gradPair_add_smul]
  have h1 := hasDerivAt_gradPair_aHessian C D (C.insert A)
  have h2 := hasDerivAt_gradPair_aHessian C D (D.insert A)
  have h3 := h1.add ((hasDerivAt_id (0 : ℝ)).mul h2)
  have h4 : HasDerivAt (fun s : ℝ => gradPair (C + s • D) ((C + s • D).insert A)) 0 0 := by
    rw [hΦ]; exact hasDerivAt_const _ _
  rw [hsplit] at h4
  have := h4.unique h3
  simp only [id, zero_smul, add_zero, one_mul, zero_mul] at this
  rw [hcrit] at this
  linarith

end

end ThirteenPlanes
