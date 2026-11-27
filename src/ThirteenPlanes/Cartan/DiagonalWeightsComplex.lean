module

public import ThirteenPlanes.Cartan.ComplexJordan
public import ThirteenPlanes.Cartan.DiagonalWeightsScalar
public import ThirteenPlanes.Peirce.SlotComplexModel

@[expose] public section

set_option backward.privateInPublic true

/-! The standard Cartan acting on the native traceless complex Hermitian matrices. -/

namespace ThirteenPlanes.Cartan

open RoundCubics Peirce
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

private def sumParameters : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ i, a i
  map_add' a b := Finset.sum_add_distrib
  map_smul' r a := by
    change (∑ i, r • a i) = r • (∑ i, a i)
    rw [Finset.smul_sum]

/-- The real trace-zero diagonal coordinates for the compact complex Cartan. -/
def complexCartanParameters : Submodule ℝ (Fin 3 → ℝ) := sumParameters.ker

private theorem sum_parameters (a : complexCartanParameters) : ∑ i, a.val i = 0 := a.property

private theorem parameter_dim : Module.finrank ℝ complexCartanParameters = 2 := by
  have hs : Function.Surjective sumParameters := by
    intro r
    refine ⟨![r, 0, 0], ?_⟩
    change (∑ i, (![r, 0, 0] : Fin 3 → ℝ) i) = r
    simp [Fin.sum_univ_three]
  have hd := sumParameters.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    Module.finrank_pi_fintype] at hd
  change Module.finrank ℝ sumParameters.ker = 2
  simp [Finset.sum_const] at hd
  omega

/-- The standard imaginary diagonal as a traceless skew-Hermitian complex matrix. -/
def complexSkewDiagonal : complexCartanParameters →ₗ[ℝ] complexSkewTracelessMatrices :=
  (show complexCartanParameters →ₗ[ℝ] ComplexMatrix3 from
    { toFun := fun a => Matrix.diagonal fun k => a.val k • Complex.I
      map_add' := fun a b => by
        rw [Matrix.diagonal_add]
        congr 1
        funext k
        exact add_smul _ _ _
      map_smul' := fun r a => by
        rw [← Matrix.diagonal_smul]
        congr 1
        funext k
        exact mul_smul _ _ _ }).codRestrict _ (fun a => by
    change (Matrix.diagonal fun k => a.val k • Complex.I)ᴴ =
        -(Matrix.diagonal fun k => a.val k • Complex.I) ∧
      Matrix.trace (Matrix.diagonal fun k => a.val k • Complex.I) = 0
    constructor
    · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
      congr 1
      funext k
      change star (a.val k • Complex.I) = -(a.val k • Complex.I)
      rw [star_smul, star_trivial, Complex.star_def, Complex.conj_I, smul_neg]
    · rw [Matrix.trace_diagonal, ← Finset.sum_smul, sum_parameters, zero_smul])

def complexStandardFull : complexCartanParameters →ₗ[ℝ] complexOperatorAlgebra :=
  complexCommutatorLinear.rangeRestrict.comp complexSkewDiagonal

/-- The standard diagonal Cartan in the unital complex operator algebra. -/
def complexStandardCartan : Submodule ℝ complexOperatorAlgebra :=
  complexStandardFull.range

private abbrev V := complexJordan.traceFree
private abbrev cmat (x : V) := fullMatrix x.val

/-- The standard diagonal action restricted to the actual traceless matrices. -/
def complexStandardRestricted : complexCartanParameters →ₗ[ℝ] SkewOperator V :=
  (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap.comp
    complexStandardFull

theorem complexStandardRestricted_range :
    complexStandardRestricted.range = complexStandardCartan.map
      (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap := by
  rw [complexStandardRestricted, LinearMap.range_comp, complexStandardCartan]

/-- Each native entry carries the two complexic weights of its row and column. -/
theorem complexStandardRestricted_matrix (a : complexCartanParameters) (x : V) (i j : Fin 3) :
    cmat ((complexStandardRestricted a).val x) i j =
      complexWeight (a.val i) (a.val j) (cmat x i j) := by
  change fullMatrix (complexCommutator (complexSkewDiagonal a) x.val) i j = _
  rw [complexCommutator_matrix]
  change ((Matrix.diagonal fun k => a.val k • Complex.I) * cmat x -
    cmat x * (Matrix.diagonal fun k => a.val k • Complex.I)) i j = _
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change _ = ((a.val i - a.val j : ℝ) : ℂ) * Complex.I * _
  simp only [Complex.real_smul, Complex.ofReal_sub]
  ring

private abbrev Coordinates := ℝ × ℝ × ℂ × ℂ × ℂ

private def coordinates : Coordinates ≃ₗ[ℝ] V :=
  complexCartanEquiv.trans complexTraceEquiv.symm.toLinearEquiv

private theorem coordinates_matrix (d e : ℝ) (p q r : ℂ) :
    cmat (coordinates (d, e, p, q, r)) = complexCartanMatrix d e p q r := by
  change TracelessHermitian3.toMatrix (complexCartanEquiv (d, e, p, q, r)) = _
  rw [complexCartanEquiv_apply, toMatrix_complexCartanField]

private theorem coordinates_inner (d e f g : ℝ) (p q r s t u : ℂ) :
    ⟪coordinates (d, e, p, q, r), coordinates (f, g, s, t, u)⟫ =
      d * f + e * g + ⟪p, s⟫ + ⟪q, t⟫ + ⟪r, u⟫ := by
  change ⟪(coordinates (d, e, p, q, r)).val, (coordinates (f, g, s, t, u)).val⟫ = _
  rw [fullInner_eq_tracePairing]
  change tracePairing (cmat (coordinates (d, e, p, q, r))) (cmat (coordinates (f, g, s, t, u))) = _
  rw [coordinates_matrix, coordinates_matrix, ← toMatrix_complexCartanField, ← toMatrix_complexCartanField]
  have h := complexCartanField_inner d e f g p q r s t u
  rw [TracelessHermitian3.inner_eq_tracePairing] at h
  exact h

private def coordAction (a : complexCartanParameters) : Module.End ℝ Coordinates :=
  (0 : Module.End ℝ ℝ).prodMap ((0 : Module.End ℝ ℝ).prodMap
    ((complexWeight (a.val 1) (a.val 2)).prodMap
      ((complexWeight (a.val 0) (a.val 2)).prodMap (complexWeight (a.val 0) (a.val 1)))))

set_option maxHeartbeats 500000 in
private theorem coordinates_action (a : complexCartanParameters) (d e : ℝ) (p q r : ℂ) :
    (complexStandardRestricted a).val (coordinates (d, e, p, q, r)) =
      coordinates (0, 0, complexWeight (a.val 1) (a.val 2) p,
        complexWeight (a.val 0) (a.val 2) q, complexWeight (a.val 0) (a.val 1) r) := by
  apply Subtype.ext
  apply fullMatrix_injective
  apply Matrix.ext
  intro i j
  change cmat ((complexStandardRestricted a).val (coordinates (d, e, p, q, r))) i j =
    cmat (coordinates (0, 0, complexWeight (a.val 1)
      (a.val 2) p, complexWeight (a.val 0)
      (a.val 2) q, complexWeight (a.val 0)
      (a.val 1) r)) i j
  rw [complexStandardRestricted_matrix, coordinates_matrix, coordinates_matrix]
  fin_cases i <;> fin_cases j <;>
    simp [complexCartanMatrix, complexSlotMatrix, complexWeight_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem coordinates_conj_action (a : complexCartanParameters) :
    coordinates.conj (coordAction a) = (complexStandardRestricted a).val := by
  apply LinearMap.ext
  intro x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, coordinates_action]
  rfl

theorem complexStandardRestricted_inner (a b : complexCartanParameters) :
    ⟪complexStandardRestricted a, complexStandardRestricted b⟫ =
      6 * ∑ i, a.val i * b.val i := by
  rw [skewOperator_inner, ← coordinates_conj_action, ← coordinates_conj_action,
    ← conj_mul, LinearMap.trace_conj']
  simp only [coordAction, LinearMap.prodMap_mul, LinearMap.trace_prodMap', zero_mul, map_zero,
    zero_add, complexWeight_trace_mul, Fin.sum_univ_three]
  have ha := sum_parameters a
  simp only [Fin.sum_univ_three] at ha
  linear_combination -2 * (b.val 0 + b.val 1 + b.val 2) * ha

private theorem complexStandardRestricted_injective : Function.Injective complexStandardRestricted := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  have hn := complexStandardRestricted_inner a a
  rw [ha, inner_zero_left] at hn
  have hz : ∑ i, a.val i * a.val i = 0 := by linarith
  apply Subtype.ext
  funext i
  change a.val i = 0
  rcases mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_self_nonneg (a.val j))).mp hz i (Finset.mem_univ i)) with h | h
  · exact h
  · exact h

theorem complexStandardCartan_dim : Module.finrank ℝ complexStandardCartan = 2 := by
  rw [complexStandardCartan, LinearMap.finrank_range_of_inj]
  · exact parameter_dim
  · intro a b h
    apply complexStandardRestricted_injective
    exact congrArg (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le) h

private theorem complexStandardRestricted_dim :
    Module.finrank ℝ complexStandardRestricted.range = 2 := by
  rw [LinearMap.finrank_range_of_inj complexStandardRestricted_injective, parameter_dim]

/-- The traceless real diagonal plane in the complexic Jordan model. -/
private def diagonalCoordinates : (ℝ × ℝ) →ₗ[ℝ] Coordinates where
  toFun p := (p.1, p.2, 0, 0, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def diagonalInclusion : (ℝ × ℝ) →ₗ[ℝ] V :=
  coordinates.toLinearMap.comp diagonalCoordinates

private theorem diagonalInclusion_apply (d e : ℝ) :
    diagonalInclusion (d, e) = coordinates (d, e, 0, 0, 0) := rfl

/-- The traceless real diagonal plane in the complex Jordan model. -/
def complexDiagonalPlane : Submodule ℝ V := diagonalInclusion.range

theorem complexDiagonalPlane_dim : Module.finrank ℝ complexDiagonalPlane = 2 := by
  rw [complexDiagonalPlane, LinearMap.finrank_range_of_inj]
  · simp [Module.finrank_prod, Module.finrank_self]
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    rw [diagonalInclusion_apply, diagonalInclusion_apply] at h
    have he := coordinates.injective h
    exact Prod.ext (congrArg (fun t : Coordinates => t.1) he) (congrArg (fun t : Coordinates => t.2.1) he)

set_option maxHeartbeats 500000 in
theorem complexStandardFixedSpace :
    fixedSpace complexStandardRestricted.range = complexDiagonalPlane := by
  rw [complexDiagonalPlane]
  ext x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  rw [mem_fixedSpace]
  constructor
  · intro h
    have hz (a : complexCartanParameters) :=
      coordinates.injective ((coordinates_action a d e p q r).symm.trans
        ((h ⟨complexStandardRestricted a, LinearMap.mem_range_self _ _⟩).trans
          (coordinates.map_zero.symm)))
    let a : complexCartanParameters := ⟨![1, 0, -1], by
      change ∑ i, (![1, 0, -1] : Fin 3 → ℝ) i = 0
      norm_num [Fin.sum_univ_three]⟩
    have hp : complexWeight 0 (-1) p = 0 := by
      simpa [a] using congrArg (fun t : Coordinates => t.2.2.1) (hz a)
    have hq : complexWeight 1 (-1) q = 0 := by
      simpa [a] using congrArg (fun t : Coordinates => t.2.2.2.1) (hz a)
    have hr : complexWeight 1 0 r = 0 := by
      simpa [a] using congrArg (fun t : Coordinates => t.2.2.2.2) (hz a)
    have h0 (b c : ℝ) (hbc : b ≠ c) (u : ℂ) (hu : complexWeight b c u = 0) : u = 0 := by
      change ((b - c : ℝ) : ℂ) * Complex.I * u = 0 at hu
      exact (mul_eq_zero.mp hu).resolve_left (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hbc)) Complex.I_ne_zero)
    rw [h0 _ _ (by norm_num) p hp, h0 _ _ (by norm_num) q hq, h0 _ _ (by norm_num) r hr]
    exact ⟨(d, e), diagonalInclusion_apply d e⟩
  · rintro ⟨⟨f, g⟩, hx⟩
    rw [diagonalInclusion_apply] at hx
    rintro ⟨_, a, rfl⟩
    change (complexStandardRestricted a).val (coordinates (d, e, p, q, r)) = 0
    rw [← hx]
    rw [coordinates_action]
    simp only [map_zero]
    exact coordinates.map_zero


/-- Membership in the fixed plane means that every native off-diagonal entry vanishes. -/
theorem mem_complexDiagonalPlane_iff (x : complexJordan.traceFree) :
    x ∈ complexDiagonalPlane ↔ ∀ i j : Fin 3, i ≠ j → fullMatrix x.val i j = 0 := by
  constructor
  · rintro ⟨⟨d, e⟩, rfl⟩ i j hij
    rw [diagonalInclusion_apply]
    change cmat (coordinates (d, e, 0, 0, 0)) i j = 0
    rw [coordinates_matrix]
    fin_cases i <;> fin_cases j <;>
      simp_all [complexCartanMatrix, complexSlotMatrix]
  · intro hx
    obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
    have hp := hx 1 2 (by decide)
    have hq := hx 0 2 (by decide)
    have hr := hx 0 1 (by decide)
    change cmat (coordinates (d, e, p, q, r)) 1 2 = 0 at hp
    change cmat (coordinates (d, e, p, q, r)) 0 2 = 0 at hq
    change cmat (coordinates (d, e, p, q, r)) 0 1 = 0 at hr
    rw [coordinates_matrix] at hp hq hr
    change (Real.sqrt 2)⁻¹ • p = (0 : ℂ) at hp
    change (Real.sqrt 2)⁻¹ • q = (0 : ℂ) at hq
    change (Real.sqrt 2)⁻¹ • r = (0 : ℂ) at hr
    have h : (Real.sqrt 2)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num))
    rw [(smul_eq_zero.mp hp).resolve_left h, (smul_eq_zero.mp hq).resolve_left h,
      (smul_eq_zero.mp hr).resolve_left h]
    exact ⟨(d, e), diagonalInclusion_apply d e⟩

private theorem complexDiagonalPlane_projection (d e : ℝ) (p q r : ℂ) :
    projection complexDiagonalPlane (coordinates (d, e, p, q, r)) = coordinates (d, e, 0, 0, 0) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [complexDiagonalPlane]
    exact ⟨(d, e), diagonalInclusion_apply d e⟩
  · rw [complexDiagonalPlane]
    rintro _ ⟨⟨f, g⟩, rfl⟩
    rw [diagonalInclusion_apply]
    change ⟪coordinates (d, e, p, q, r) - coordinates (d, e, 0, 0, 0),
      coordinates (f, g, 0, 0, 0)⟫ = 0
    have hsub : coordinates (d, e, p, q, r) - coordinates (d, e, 0, 0, 0) =
        coordinates (d - d, e - e, p - 0, q - 0, r - 0) :=
      (map_sub coordinates ((d, e, p, q, r) : Coordinates) ((d, e, 0, 0, 0) : Coordinates)).symm
    rw [hsub, coordinates_inner]
    simp

private def basisParameters : Fin 2 → complexCartanParameters :=
  ![⟨![1, -1, 0], by
        change (∑ i, (![1, -1, 0] : Fin 3 → ℝ) i) = 0
        norm_num [Fin.sum_univ_three]⟩,
    ⟨![1, 1, -2], by
        change (∑ i, (![1, 1, -2] : Fin 3 → ℝ) i) = 0
        norm_num [Fin.sum_univ_three]⟩]

private def basisNormSq : Fin 2 → ℝ := ![12, 36]

private theorem complexStandardRestricted_commute (a b : complexCartanParameters) :
    Commute (complexStandardRestricted a).val (complexStandardRestricted b).val := by
  show (complexStandardRestricted a).val * (complexStandardRestricted b).val =
    (complexStandardRestricted b).val * (complexStandardRestricted a).val
  apply LinearMap.ext
  intro x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  simp only [mul_apply_eq_comp, coordinates_action]
  have h (a b c d : ℝ) (z : ℂ) :
      complexWeight a b (complexWeight c d z) = complexWeight c d (complexWeight a b z) := by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, complexWeight_comp_apply,
      complexWeight_comp_apply, mul_comm (a - b)]
  simp only [h (a.val 1) (a.val 2), h (a.val 0) (a.val 2), h (a.val 0) (a.val 1)]

set_option maxHeartbeats 700000 in
theorem complexStandardRestricted_casimir :
    operatorCasimir complexStandardRestricted.range =
      (1 / 3 : ℝ) • (LinearMap.id - projection (fixedSpace complexStandardRestricted.range)) := by
  let A (i : Fin 2) : complexStandardRestricted.range :=
    ⟨complexStandardRestricted (basisParameters i), LinearMap.mem_range_self _ _⟩
  have hA (i j : Fin 2) : ⟪A i, A j⟫ = if i = j then basisNormSq i else 0 := by
    change ⟪complexStandardRestricted (basisParameters i),
      complexStandardRestricted (basisParameters j)⟫ = _
    rw [complexStandardRestricted_inner, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> norm_num [basisParameters, basisNormSq]
  rw [operatorCasimir_of_orthogonalBasis _ A basisNormSq
    (complexStandardRestricted_dim.trans (Fintype.card_fin 2).symm)
    (fun i => by fin_cases i <;> norm_num [basisNormSq]) hA, complexStandardFixedSpace]
  apply LinearMap.ext
  intro x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply, mul_apply_eq_comp,
    LinearMap.sub_apply, LinearMap.id_apply, complexDiagonalPlane_projection, Fin.sum_univ_two]
  simp only [A, coordinates_action]
  have hsquare (b c : ℝ) (z : ℂ) :
      complexWeight b c (complexWeight b c z) = (-((b - c) * (b - c))) • z :=
    complexWeight_comp_apply b c b c z
  simp only [hsquare, basisParameters, basisNormSq]
  norm_num
  simp only [← map_sub, ← map_smul, ← map_add, ← map_neg]
  apply congrArg coordinates
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  all_goals dsimp
  · ring
  · ring
  all_goals
    simp
    ring

/-- The standard complex Cartan is of frame type for the actual trace normalization. -/
theorem complexStandardFrameType :
    IsFrameType (complexStandardCartan.map
      (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap)
      2 (1 / 3) := by
  rw [← complexStandardRestricted_range]
  refine ⟨?_, complexStandardRestricted_dim, ?_, complexStandardRestricted_casimir⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact complexStandardRestricted_commute a b
  · rw [complexStandardFixedSpace, complexDiagonalPlane_dim]

@[simp] theorem complexSkewDiagonal_matrix (a : complexCartanParameters) :
    (complexSkewDiagonal a).val = Matrix.diagonal (fun k => a.val k • Complex.I) := rfl

/-- The standard complex imaginary diagonal is self-centralizing among traceless skew matrices. -/
theorem complexSkewDiagonal_centralizer (A : complexSkewTracelessMatrices)
    (h : ∀ a : complexCartanParameters, Commute A.val (complexSkewDiagonal a).val) :
    A ∈ complexSkewDiagonal.range := by
  have hskew : A.valᴴ = -A.val := A.property.1
  have htrace : Matrix.trace A.val = 0 := A.property.2
  let a : complexCartanParameters := ⟨![1, 0, -1], by
    change (∑ i, (![1, 0, -1] : Fin 3 → ℝ) i) = 0
    norm_num [Fin.sum_univ_three]⟩
  refine ⟨⟨fun i => (A.val i i).im, ?_⟩, ?_⟩
  · have e := congrArg Complex.im htrace
    change (∑ i, (A.val i i).im) = 0
    simpa [Matrix.trace, Fin.sum_univ_three] using e
  apply Subtype.ext
  rw [complexSkewDiagonal_matrix]
  apply Matrix.ext
  intro i j
  change (Matrix.diagonal (fun k => (A.val k k).im • Complex.I)) i j = A.val i j
  by_cases hij : i = j
  · subst j
    have e := congrArg (fun M : ComplexMatrix3 => (M i i).re) hskew
    have hre : (A.val i i).re = 0 := by
      simp [Matrix.conjTranspose_apply] at e
      linarith
    rw [Matrix.diagonal_apply_eq]
    apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, hre]
  · have hdiff : a.val j ≠ a.val i := by
      fin_cases i <;> fin_cases j <;> simp_all [a] <;> norm_num
    have e := congrArg (fun M : ComplexMatrix3 => M i j) (h a).eq
    rw [complexSkewDiagonal_matrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    have hz : ((a.val j - a.val i : ℝ) : ℂ) * Complex.I * A.val i j = 0 := by
      simp only [Complex.real_smul, Complex.ofReal_sub] at e ⊢
      linear_combination e
    exact (Matrix.diagonal_apply_ne _ hij).trans
      ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hdiff)) Complex.I_ne_zero)).symm

end

end ThirteenPlanes.Cartan
