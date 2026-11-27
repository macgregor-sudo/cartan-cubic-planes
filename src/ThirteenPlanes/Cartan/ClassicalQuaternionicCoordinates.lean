module

public import ThirteenPlanes.Cartan.ClassicalQuaternionicLie
public import ThirteenPlanes.Cartan.DiagonalWeightsScalar
public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! The adjoint trace in block coordinates on compact sp(3). -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB LieAlgebra
open scoped Matrix BigOperators

noncomputable section

private abbrev ImaginaryCoords := ℝ × ℝ × ℝ
private abbrev SkewCoords := (ImaginaryCoords × ImaginaryCoords × ImaginaryCoords) × (Q × Q × Q)

private def imaginary (x : ImaginaryCoords) : Q := ⟨0, x.1, x.2.1, x.2.2⟩

private def imaginaryCoords (q : Q) : ImaginaryCoords := (q.imI, q.imJ, q.imK)

private def skewFromCoords (x : SkewCoords) : QMat :=
  ![![imaginary x.1.1, x.2.1, x.2.2.1],
    ![-star x.2.1, imaginary x.1.2.1, x.2.2.2],
    ![-star x.2.2.1, -star x.2.2.2, imaginary x.1.2.2]]

private def skewToCoords (A : QMat) : SkewCoords :=
  ((imaginaryCoords (A 0 0), imaginaryCoords (A 1 1), imaginaryCoords (A 2 2)),
    (A 0 1, A 0 2, A 1 2))

private theorem skewFromCoords_skew (x : SkewCoords) : (skewFromCoords x)ᴴ = -skewFromCoords x := by
  apply Matrix.ext
  intro i j
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp [skewFromCoords, imaginary]

private theorem skewFromCoords_inverse (A : compactSp3) :
    skewFromCoords (skewToCoords A.val) = A.val := by
  have hs (i j : Fin 3) : star (A.val j i) = -A.val i j :=
    congrFun (congrFun A.property i) j
  have hd (i : Fin 3) : imaginary (imaginaryCoords (A.val i i)) = A.val i i := by
    have h := congrArg (fun q : Q => q.re) (hs i i)
    ext <;> simp [imaginary, imaginaryCoords] at h ⊢
    linarith
  have hneg (i j : Fin 3) : -star (A.val j i) = A.val i j := neg_eq_iff_eq_neg.mpr (hs i j)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [skewFromCoords, skewToCoords, hd, hneg]

private def skewCoordinates : compactSp3 ≃ₗ[ℝ] SkewCoords where
  toFun A := skewToCoords A.val
  invFun x := ⟨skewFromCoords x, skewFromCoords_skew x⟩
  left_inv A := Subtype.ext (skewFromCoords_inverse A)
  right_inv x := by
    rcases x with ⟨⟨d₀, d₁, d₂⟩, p, q, r⟩
    rcases d₀ with ⟨a₀, b₀, c₀⟩
    rcases d₁ with ⟨a₁, b₁, c₁⟩
    rcases d₂ with ⟨a₂, b₂, c₂⟩
    rfl
  map_add' A B := rfl
  map_smul' r A := rfl

theorem compactSp3_finrank : Module.finrank ℝ compactSp3 = 21 := by
  rw [skewCoordinates.finrank_eq]
  simp [Module.finrank_prod, Quaternion.finrank_eq_four]

/-- The diagonal model of the rank-three compact torus. -/
def compactSp3Diagonal (a : Fin 3 → ℝ) : compactSp3 :=
  ⟨quaternionicStandardDiagonal a, by
    change (Matrix.diagonal (fun k => a k • qi))ᴴ = -(Matrix.diagonal (fun k => a k • qi))
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
    congr 1
    funext k
    change star (a k • qi) = -(a k • qi)
    rw [Quaternion.star_smul, show star qi = -qi by ext <;> simp [qi], smul_neg]⟩

@[simp] theorem compactSp3Diagonal_val (a : Fin 3 → ℝ) :
    (compactSp3Diagonal a).val = Matrix.diagonal (fun k => a k • qi) := rfl

private def imagRotation (a : ℝ) : Module.End ℝ ImaginaryCoords where
  toFun x := (0, -2 * a * x.2.2, 2 * a * x.2.1)
  map_add' x y := by
    apply Prod.ext
    · change (0 : ℝ) = 0 + 0
      norm_num
    · apply Prod.ext
      · change -2 * a * (x.2.2 + y.2.2) = -2 * a * x.2.2 + (-2 * a * y.2.2)
        ring
      · change 2 * a * (x.2.1 + y.2.1) = 2 * a * x.2.1 + 2 * a * y.2.1
        ring
  map_smul' r x := by
    apply Prod.ext
    · change (0 : ℝ) = r * 0
      norm_num
    · apply Prod.ext
      · change -2 * a * (r * x.2.2) = r * (-2 * a * x.2.2)
        ring
      · change 2 * a * (r * x.2.1) = r * (2 * a * x.2.1)
        ring

private theorem trace_imagRotation_mul (a b : ℝ) :
    LinearMap.trace ℝ ImaginaryCoords (imagRotation a * imagRotation b) = -8 * a * b := by
  have h : imagRotation a * imagRotation b = LinearMap.prodMap (0 : Module.End ℝ ℝ)
      ((-4 * a * b) • (LinearMap.id : Module.End ℝ (ℝ × ℝ))) := by
    apply LinearMap.ext
    intro x
    change (0, -2*a*(2*b*x.2.1), 2*a*(-2*b*x.2.2)) =
      (0, (-4*a*b)*x.2.1, (-4*a*b)*x.2.2)
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> ring
  rw [h, LinearMap.trace_prodMap', map_zero, zero_add, map_smul, LinearMap.trace_id]
  simp only [Module.finrank_prod, Module.finrank_self, Nat.cast_add, Nat.cast_one, smul_eq_mul]
  ring

private def blockAdjoint (a : Fin 3 → ℝ) : Module.End ℝ SkewCoords :=
  LinearMap.prodMap
    (LinearMap.prodMap (imagRotation (a 0))
      (LinearMap.prodMap (imagRotation (a 1)) (imagRotation (a 2))))
    (LinearMap.prodMap (quaternionWeight (a 0) (a 1))
      (LinearMap.prodMap (quaternionWeight (a 0) (a 2)) (quaternionWeight (a 1) (a 2))))

private theorem skewCoordinates_ad (a : Fin 3 → ℝ) (X : compactSp3) :
    skewCoordinates (⁅compactSp3Diagonal a, X⁆ : compactSp3) =
      blockAdjoint a (skewCoordinates X) := by
  have h (i j : Fin 3) : ((⁅compactSp3Diagonal a, X⁆ : compactSp3).val) i j =
      (a i • qi) * X.val i j - X.val i j * (a j • qi) := by
    change ((compactSp3Diagonal a).val * X.val - X.val * (compactSp3Diagonal a).val) i j = _
    rw [compactSp3Diagonal_val, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change skewToCoords ((⁅compactSp3Diagonal a,X⁆ : compactSp3).val) =
    blockAdjoint a (skewToCoords X.val)
  have qweight (r s : ℝ) (q : Q) :
      (r • qi) * q - q * (s • qi) = quaternionWeight r s q := by
    apply Quaternion.ext <;> simp [quaternionWeight_apply, qi] <;> ring
  have qdiag (r : ℝ) (q : Q) :
      imaginaryCoords (quaternionWeight r r q) = imagRotation r (imaginaryCoords q) := by
    apply Prod.ext
    · simp [imaginaryCoords, quaternionWeight_apply, imagRotation]
    · apply Prod.ext
      · change (quaternionWeight r r q).imJ = -2 * r * q.imK
        rw [quaternionWeight_apply]
        change -(r + r) * q.imK = -2 * r * q.imK
        ring
      · change (quaternionWeight r r q).imK = 2 * r * q.imJ
        rw [quaternionWeight_apply]
        change (r + r) * q.imJ = 2 * r * q.imJ
        ring
  simp only [blockAdjoint, LinearMap.prodMap_apply, skewToCoords, h, qweight, qdiag]

private theorem conj_ad_diagonal (a : Fin 3 → ℝ) :
    skewCoordinates.conj (LieAlgebra.ad ℝ compactSp3 (compactSp3Diagonal a)) = blockAdjoint a := by
  apply LinearMap.ext
  intro x
  change skewCoordinates (⁅compactSp3Diagonal a, skewCoordinates.symm x⁆ : compactSp3) = _
  rw [skewCoordinates_ad, LinearEquiv.apply_symm_apply]

private theorem prodMap_mul {X Y : Type} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (f g : Module.End ℝ X) (h k : Module.End ℝ Y) :
    LinearMap.prodMap f h * LinearMap.prodMap g k = LinearMap.prodMap (f * g) (h * k) :=
  LinearMap.ext fun _ => rfl

private theorem trace_blockAdjoint_mul (a b : Fin 3 → ℝ) :
    LinearMap.trace ℝ SkewCoords (blockAdjoint a * blockAdjoint b) =
      -16 * ∑ i, a i * b i := by
  simp only [blockAdjoint, prodMap_mul, LinearMap.trace_prodMap', trace_imagRotation_mul,
    quaternionWeight_trace_mul, Fin.sum_univ_three]
  ring

theorem compactSp3_killing_diagonal (a b : Fin 3 → ℝ) :
    killingForm ℝ compactSp3 (compactSp3Diagonal a) (compactSp3Diagonal b) =
      -16 * ∑ i, a i * b i := by
  rw [killingForm_apply_apply, ← Module.End.mul_eq_comp, ← LinearMap.trace_conj' _ skewCoordinates,
    conj_mul, conj_ad_diagonal, conj_ad_diagonal, trace_blockAdjoint_mul]

end
end ThirteenPlanes.Cartan
