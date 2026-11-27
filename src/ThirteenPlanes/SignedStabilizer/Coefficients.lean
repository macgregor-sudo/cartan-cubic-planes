module

public import ThirteenPlanes.SignedStabilizer.Complexify
public import ThirteenPlanes.SignedSupport

@[expose] public section

set_option backward.privateInPublic true

/-! Coefficient equations for a skew infinitesimal symmetry of the signed interaction cubic,
written in the complex matrix of the endomorphism. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace SignedStabilizer

local notation "z" => signedCoordinates

/-- Coefficient table of the interaction cubic `c_t` in the charge coordinates. -/
def ctCoeff (t : ℝ) (i j k : NonzeroCharge) : ℂ :=
  ((1 - t : ℝ) : ℂ) * signedDiagonalCoefficient i j k + (t : ℂ) * signedCoefficient i j k

private theorem apply_sub (h g : SymmetricCubic SignedField) (x y w : SignedField) :
    (h - g).apply x y w = h.apply x y w - g.apply x y w := by
  have := SymmetricCubic.apply_add (h - g) g x y w
  have e : h - g + g = h := sub_add_cancel h g
  rw [e] at this
  linarith

/-- The complex coefficient sum of the interaction cubic on three fields. -/
def ctSum (t : ℝ) (a b c : SignedField) : ℂ :=
  ∑ i, ∑ j, ∑ k, ctCoeff t i j k * z a i * z b j * z c k

theorem interaction_apply (t : ℝ) (a b c : SignedField) :
    (interactionCubic signedPair t).apply a b c = (ctSum t a b c).re := by
  have hterm : ∀ i j k, (ctCoeff t i j k * z a i * z b j * z c k).re =
      (1 - t) * (signedDiagonalCoefficient i j k * z a i * z b j * z c k).re +
        t * (signedCoefficient i j k * z a i * z b j * z c k).re := by
    intro i j k
    rw [show ctCoeff t i j k * z a i * z b j * z c k =
      ((1 - t : ℝ) : ℂ) * (signedDiagonalCoefficient i j k * z a i * z b j * z c k) +
        (t : ℂ) * (signedCoefficient i j k * z a i * z b j * z c k) by unfold ctCoeff; ring]
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp only [interactionCubic, coupling_apply, signedPair, SymmetricCubic.apply_add,
    SymmetricCubic.apply_smul, apply_sub, signedEqualCubic_apply, signedDiagonalCubic_apply,
    ctSum, Complex.re_sum, hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem diag_opposite (i j k : NonzeroCharge) :
    signedDiagonalCoefficient (oppositeCharge i) (oppositeCharge j) (oppositeCharge k) =
      signedDiagonalCoefficient i j k := by
  simp only [signedDiagonalCoefficient, oppositeCharge_injective.eq_iff]

private theorem diag_star (i j k : NonzeroCharge) :
    star (signedDiagonalCoefficient i j k) = signedDiagonalCoefficient i j k := by
  unfold signedDiagonalCoefficient
  split_ifs <;> simp

theorem ctCoeff_opposite (t : ℝ) (i j k : NonzeroCharge) :
    ctCoeff t (oppositeCharge i) (oppositeCharge j) (oppositeCharge k) = star (ctCoeff t i j k) := by
  simp only [ctCoeff, diag_opposite, signedCoefficient_opposite, star_add, star_mul',
    diag_star, Complex.star_def, Complex.conj_ofReal]

/-- The complex coefficient sum is real on real fields. -/
theorem ctSum_real (t : ℝ) (a b c : SignedField) : ctSum t a b c = ((ctSum t a b c).re : ℂ) := by
  rw [eq_comm, ← Complex.conj_eq_iff_re]
  set F : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ :=
    fun i j k => ctCoeff t i j k * z a i * z b j * z c k with hF
  have hstar : starRingEnd ℂ (ctSum t a b c) =
      ∑ i, ∑ j, ∑ k, F (oppositeCharge i) (oppositeCharge j) (oppositeCharge k) := by
    simp only [ctSum, map_sum, map_mul, hF, ctCoeff_opposite, signedCoordinates_opposite,
      Complex.star_def]
  rw [hstar]
  have h3 : ∀ i j, ∑ k, F i j (oppositeCharge k) = ∑ k, F i j k := fun i j => sum_opposite (F i j)
  have h2 : ∀ i, ∑ j, ∑ k, F i (oppositeCharge j) k = ∑ j, ∑ k, F i j k :=
    fun i => sum_opposite (fun j => ∑ k, F i j k)
  have h1 : ∑ i, ∑ j, ∑ k, F (oppositeCharge i) j k = ∑ i, ∑ j, ∑ k, F i j k :=
    sum_opposite (fun i => ∑ j, ∑ k, F i j k)
  simp only [h3, h2, h1]
  rfl

theorem ctSum_eq_apply (t : ℝ) (a b c : SignedField) :
    ctSum t a b c = ((interactionCubic signedPair t).apply a b c : ℂ) := by
  rw [interaction_apply]; exact ctSum_real t a b c

/-- The complex-trilinear form with a given coefficient table. -/
def triForm (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ) :
    (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ :=
  (Pi.basisFun ℂ NonzeroCharge).constr ℂ fun i => (Pi.basisFun ℂ NonzeroCharge).constr ℂ fun j =>
    (Pi.basisFun ℂ NonzeroCharge).constr ℂ fun k => c i j k

theorem triForm_apply (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (Z W U : NonzeroCharge → ℂ) :
    triForm c Z W U = ∑ i, ∑ j, ∑ k, c i j k * Z i * W j * U k := by
  simp only [triForm, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Insertion of a complex matrix into the three slots of a complex-trilinear form. -/
def insertForm (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (M : Matrix NonzeroCharge NonzeroCharge ℂ) :
    (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ :=
  triForm c ∘ₗ M.mulVecLin + ((triForm c).flip ∘ₗ M.mulVecLin).flip +
    (triForm c).compr₂ (LinearMap.lcomp ℂ ℂ M.mulVecLin)

theorem insertForm_apply (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (M : Matrix NonzeroCharge NonzeroCharge ℂ) (Z W U : NonzeroCharge → ℂ) :
    insertForm c M Z W U =
      triForm c (M.mulVec Z) W U + triForm c Z (M.mulVec W) U + triForm c Z W (M.mulVec U) :=
  rfl

theorem mulVec_single (M : Matrix NonzeroCharge NonzeroCharge ℂ) (x y : NonzeroCharge) :
    M.mulVec (Pi.single x 1) y = M y x := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem triForm_s1 (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (V : NonzeroCharge → ℂ) (j k : NonzeroCharge) :
    triForm c V (Pi.single j 1) (Pi.single k 1) = ∑ i, V i * c i j k := by
  rw [triForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.single_apply, mul_comm]

private theorem triForm_s2 (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (V : NonzeroCharge → ℂ) (i k : NonzeroCharge) :
    triForm c (Pi.single i 1) V (Pi.single k 1) = ∑ j, V j * c i j k := by
  rw [triForm_apply]
  simp [Pi.single_apply, mul_comm]

private theorem triForm_s3 (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (V : NonzeroCharge → ℂ) (i j : NonzeroCharge) :
    triForm c (Pi.single i 1) (Pi.single j 1) V = ∑ k, V k * c i j k := by
  rw [triForm_apply]
  simp [Pi.single_apply, mul_comm]

private theorem triForm_single (c : NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ)
    (M : Matrix NonzeroCharge NonzeroCharge ℂ) (x x' x'' : NonzeroCharge) :
    insertForm c M (Pi.single x 1) (Pi.single x' 1) (Pi.single x'' 1) =
      ∑ y, M y x * c y x' x'' + ∑ y, M y x' * c x y x'' + ∑ y, M y x'' * c x x' y := by
  rw [insertForm_apply, triForm_s1, triForm_s2, triForm_s3]
  simp only [mulVec_single]

/-- An infinitesimal symmetry of `c_t` gives linear equations on its complex matrix. -/
theorem insert_coefficient_eq (t : ℝ) (A : SignedField →ₗ[ℝ] SignedField)
    (hins : (interactionCubic signedPair t).insert A = 0) (x x' x'' : NonzeroCharge) :
    ∑ y, mat A y x * ctCoeff t y x' x'' + ∑ y, mat A y x' * ctCoeff t x y x'' +
      ∑ y, mat A y x'' * ctCoeff t x x' y = 0 := by
  have hT : insertForm (ctCoeff t) (mat A) = 0 := by
    apply trilinear_ext_of_real
    intro a b c
    rw [insertForm_apply, ← coord_apply_eq_mulVec, ← coord_apply_eq_mulVec,
      ← coord_apply_eq_mulVec, triForm_apply, triForm_apply, triForm_apply]
    change ctSum t (A a) b c + ctSum t a (A b) c + ctSum t a b (A c) = 0
    rw [ctSum_eq_apply, ctSum_eq_apply, ctSum_eq_apply]
    have := congrArg (fun g : SymmetricCubic SignedField => g.apply a b c) hins
    simp only [SymmetricCubic.apply_insert, SymmetricCubic.apply_zero] at this
    exact_mod_cast this
  have := LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun hT (Pi.single x 1))
    (Pi.single x' 1)) (Pi.single x'' 1)
  rw [triForm_single] at this
  simpa using this

/-- The real inner product in charge coordinates. -/
theorem inner_eq (a b : SignedField) :
    ⟪a, b⟫ = 3 * (∑ i, star (z a i) * z b i).re := by
  change ⟪signedFieldEmbedding a, signedFieldEmbedding b⟫ = _
  simp only [signedFieldEmbedding, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  simp only [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.inner, mul_comm]

/-- The complex-bilinear form pairing opposite grades. -/
def biForm : (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ :=
  (Pi.basisFun ℂ NonzeroCharge).constr ℂ fun i => (Pi.basisFun ℂ NonzeroCharge).constr ℂ fun j =>
    if i = oppositeCharge j then 1 else 0

theorem biForm_apply (Z W : NonzeroCharge → ℂ) :
    biForm Z W = ∑ j, Z (oppositeCharge j) * W j := by
  simp only [biForm, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  have hin : ∀ x, (∑ x1, if x = oppositeCharge x1 then W x1 else 0) = W (oppositeCharge x) := by
    intro x
    rw [Finset.sum_eq_single (oppositeCharge x)]
    · simp [oppositeCharge_opposite]
    · intro b _ hb
      have : ¬ x = oppositeCharge b := fun h => hb (by rw [h, oppositeCharge_opposite])
      simp [this]
    · simp
  simp only [hin]
  rw [← sum_opposite]
  simp only [oppositeCharge_opposite]

theorem biForm_real (a b : SignedField) :
    biForm (z a) (z b) = ((⟪a, b⟫ / 3 : ℝ) : ℂ) := by
  rw [inner_eq, biForm_apply]
  simp only [signedCoordinates_opposite]
  set P := ∑ j, star (z a j) * z b j with hP
  have hreal : starRingEnd ℂ P = P := by
    rw [hP, map_sum]
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
    rw [← sum_opposite]
    simp only [signedCoordinates_opposite, Complex.star_def, Complex.conj_conj]
  rw [Complex.conj_eq_iff_re] at hreal
  rw [show ((3 * P.re / 3 : ℝ) : ℂ) = (P.re : ℂ) by push_cast; ring]
  exact hreal.symm

/-- Insertion of a complex matrix into both slots of the bilinear form. -/
def skewForm (M : Matrix NonzeroCharge NonzeroCharge ℂ) :
    (NonzeroCharge → ℂ) →ₗ[ℂ] (NonzeroCharge → ℂ) →ₗ[ℂ] ℂ :=
  biForm ∘ₗ M.mulVecLin + (biForm.flip ∘ₗ M.mulVecLin).flip

/-- A skew real endomorphism has a skew complex matrix for the opposite-grade pairing. -/
theorem skew_coefficient_eq (A : SignedField →ₗ[ℝ] SignedField)
    (hskew : ∀ u v, ⟪A u, v⟫ = -⟪u, A v⟫) (x x' : NonzeroCharge) :
    mat A (oppositeCharge x') x + mat A (oppositeCharge x) x' = 0 := by
  have hT : skewForm (mat A) = 0 := by
    apply bilinear_ext_of_real
    intro a b
    change biForm ((mat A).mulVec (z a)) (z b) + biForm (z a) ((mat A).mulVec (z b)) = 0
    rw [← coord_apply_eq_mulVec, ← coord_apply_eq_mulVec, biForm_real, biForm_real, hskew]
    push_cast
    ring
  have := LinearMap.congr_fun (LinearMap.congr_fun hT (Pi.single x 1)) (Pi.single x' 1)
  change biForm ((mat A).mulVec (Pi.single x 1)) (Pi.single x' 1) +
    biForm (Pi.single x 1) ((mat A).mulVec (Pi.single x' 1)) = 0 at this
  simp only [biForm_apply, mulVec_single, Pi.single_apply,
    mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, oppositeCharge_eq_iff] at this
  exact this

end SignedStabilizer

end

end ThirteenPlanes
