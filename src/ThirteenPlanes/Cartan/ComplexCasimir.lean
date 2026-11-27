module

public import ThirteenPlanes.Cartan.ComplexCommutant
public import ThirteenPlanes.PilotContractions

@[expose] public section

set_option backward.privateInPublic true

/-! The full Casimir of the actual special-unitary commutator representation. -/

namespace ThirteenPlanes.Cartan

open scoped Matrix
open RoundCubics

noncomputable section

/-- Conjugation preserves the actual traceless skew-Hermitian matrix space. -/
def complexConjugatedSkew (U : ComplexUnitary3) (A : complexSkewTracelessMatrices) :
    complexSkewTracelessMatrices :=
  ⟨complexMatrixAd U A.val, by
    change star (complexMatrixAd U A.val) = -complexMatrixAd U A.val ∧
      Matrix.trace (complexMatrixAd U A.val) = 0
    constructor
    · rw [← map_star, show star A.val = -A.val from A.property.1, map_neg]
    · rw [complexMatrixAd_preserves_trace]
      exact A.property.2⟩

/-- The commutator representation on the actual trace kernel. -/
def complexRestrictedOperatorAlgebra : Submodule ℝ (SkewOperator complexJordan.traceFree) :=
  LinearMap.range (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap

/-- The native traceless restriction of commutation by one skew-Hermitian matrix. -/
def complexRestrictedCommutator (A : complexSkewTracelessMatrices) : SkewOperator complexJordan.traceFree :=
  complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le
    ⟨complexCommutatorLinear A, ⟨A, rfl⟩⟩

@[simp] theorem complexRestrictedCommutator_matrix (A : complexSkewTracelessMatrices)
    (x : complexJordan.traceFree) :
    fullMatrix ((complexRestrictedCommutator A).val x).val =
      A.val * fullMatrix x.val - fullMatrix x.val * A.val := complexCommutator_matrix A x.val

private theorem complexRestrictedOperatorAlgebra_mem (D : SkewOperator complexJordan.traceFree) :
    D ∈ complexRestrictedOperatorAlgebra ↔ ∃ A, complexRestrictedCommutator A = D := by
  constructor
  · rintro ⟨⟨D, ⟨A, rfl⟩⟩, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨⟨complexCommutatorLinear A, ⟨A, rfl⟩⟩, rfl⟩

/-- Actual matrix conjugation intertwines the represented commutators. -/
theorem complex_conjugate_restrictedCommutator (U : ComplexUnitary3) (A : complexSkewTracelessMatrices) :
    conjugateSkew ((complexUnitaryAction U).traceAction complexJordan) (complexRestrictedCommutator A) =
      complexRestrictedCommutator (complexConjugatedSkew U A) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply fullMatrix_injective
  change fullMatrix (((complexUnitaryAction U).traceAction complexJordan)
    ((complexRestrictedCommutator A).val
      (((complexUnitaryAction U).traceAction complexJordan).symm x))).val = _
  rw [complexUnitaryAction_trace_matrix, complexRestrictedCommutator_matrix,
    complexRestrictedCommutator_matrix]
  have ht : fullMatrix ((((complexUnitaryAction U).traceAction complexJordan).symm x).val) =
      complexMatrixAd (star U) (fullMatrix x.val) := complexUnitaryAction_matrix (star U) x.val
  rw [ht, map_sub, map_mul, map_mul]
  have h := complexMatrixAd_inv (star U) (fullMatrix x.val)
  rw [star_star] at h
  rw [h]
  rfl

/-- All unitary conjugations normalize the actual traceless commutator operators. -/
theorem complexRestrictedOperatorAlgebra_normalizes (U : ComplexUnitary3) :
    complexRestrictedOperatorAlgebra.map
      (conjugateSkew ((complexUnitaryAction U).traceAction complexJordan)).toLinearMap =
        complexRestrictedOperatorAlgebra := by
  apply le_antisymm
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨A, rfl⟩ := (complexRestrictedOperatorAlgebra_mem D).mp hD
    apply (complexRestrictedOperatorAlgebra_mem _).mpr
    exact ⟨complexConjugatedSkew U A, (complex_conjugate_restrictedCommutator U A).symm⟩
  · intro D hD
    obtain ⟨A, rfl⟩ := (complexRestrictedOperatorAlgebra_mem D).mp hD
    refine ⟨complexRestrictedCommutator (complexConjugatedSkew (star U) A),
      (complexRestrictedOperatorAlgebra_mem _).mpr ⟨_, rfl⟩, ?_⟩
    change conjugateSkew ((complexUnitaryAction U).traceAction complexJordan)
      (complexRestrictedCommutator (complexConjugatedSkew (star U) A)) = _
    rw [complex_conjugate_restrictedCommutator]
    congr 1
    apply Subtype.ext
    change complexMatrixAd U (complexMatrixAd (star U) A.val) = A.val
    have h := complexMatrixAd_inv (star U) A.val
    rw [star_star] at h
    exact h

/-- The full complex Casimir is the dimension ratio in the literal trace metric of §7. -/
theorem complex_full_casimir : operatorCasimir complexRestrictedOperatorAlgebra =
    (Module.finrank ℝ complexRestrictedOperatorAlgebra /
      (Module.finrank ℝ complexJordan.traceFree : ℝ)) • LinearMap.id := by
  apply fullCasimir_eq_finrank_div
    (fun U : ComplexSpecialUnitary3 => (complexSU3Action U).traceAction complexJordan)
  · rw [complexTraceEquiv.finrank_eq, fourPlane_dimension]
    norm_num
  · intro U
    exact complexRestrictedOperatorAlgebra_normalizes (⟨U.val, U.property.1⟩ : ComplexUnitary3)
  · exact complex_scalar_commutant

private theorem complex_skewTraceless_zero_of_commutes (A : complexSkewTracelessMatrices)
    (commutes : ∀ X : ComplexMatrix3, X.IsHermitian → A.val * X = X * A.val) : A = 0 := by
  have hoff (i j : Fin 3) (hij : i ≠ j) : A.val i j = 0 := by
    let d (k : Fin 3) : ℂ := if k = j then 1 else 0
    have hd : (Matrix.diagonal d).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      congr 1
      funext k
      by_cases hk : k = j <;> simp [d, hk]
    have h := congrArg (fun X : ComplexMatrix3 => X i j) (commutes (Matrix.diagonal d) hd)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa [d, hij] using h
  have hAd : A.val = Matrix.diagonal (fun i => A.val i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hdiag (i j : Fin 3) : A.val i i = A.val j j := by
    let X : ComplexMatrix3 := Matrix.of fun a b => if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0
    have hX : X.IsHermitian := by
      rw [Matrix.IsHermitian]
      ext a b
      change star (if (b = i ∧ a = j) ∨ (b = j ∧ a = i) then (1 : ℂ) else 0) =
        if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0
      by_cases h : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
      · have h' : (b = i ∧ a = j) ∨ (b = j ∧ a = i) := by tauto
        simp [h, h']
      · have h' : ¬((b = i ∧ a = j) ∨ (b = j ∧ a = i)) := by tauto
        simp [h, h']
    have hm := congrArg (fun M : ComplexMatrix3 => M i j) (commutes X hX)
    have hc : X i j = 1 := by simp [X]
    change (A.val * X) i j = (X * A.val) i j at hm
    nth_rw 1 2 [hAd] at hm
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hc, mul_one, one_mul] at hm
    exact hm
  have hn : A.val 0 0 = 0 := by
    have ht := A.property.2
    rw [Matrix.trace, Fin.sum_univ_three] at ht
    change A.val 0 0 + A.val 1 1 + A.val 2 2 = 0 at ht
    rw [hdiag 1 0, hdiag 2 0] at ht
    linear_combination ht / 3
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    exact (hdiag i 0).trans hn
  · exact hoff i j hij

/-- Commutation on the full Hermitian carrier is faithful for traceless skew-Hermitian matrices. -/
theorem complexCommutatorLinear_injective : Function.Injective complexCommutatorLinear := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro A hA
  have hz : complexCommutatorLinear A = 0 := hA
  apply complex_skewTraceless_zero_of_commutes A
  intro X hX
  have h := congrArg (fun D : SkewOperator FullHermitian => fullMatrix (D.val (ofFullMatrix X hX))) hz
  change fullMatrix (complexCommutator A (ofFullMatrix X hX)) = fullMatrix 0 at h
  rw [complexCommutator_matrix, fullMatrix_ofFullMatrix, map_zero] at h
  exact sub_eq_zero.mp h

/-- Multiplication by `i` identifies the actual complex traceless Hermitian and skew-Hermitian carriers. -/
def complexTraceToSkewEquiv : TracelessHermitian3 ≃ₗ[ℝ] complexSkewTracelessMatrices where
  toFun x := ⟨Complex.I • TracelessHermitian3.toMatrix x, by
    change (Complex.I • TracelessHermitian3.toMatrix x)ᴴ = -(Complex.I • TracelessHermitian3.toMatrix x) ∧
      Matrix.trace (Complex.I • TracelessHermitian3.toMatrix x) = 0
    constructor
    · simp [Matrix.conjTranspose_smul, x.isHermitian.eq]
    · simp [Matrix.trace_smul]⟩
  invFun y := TracelessHermitian3.ofMatrix ((-Complex.I) • y.val) (by
      change (((-Complex.I) • y.val)ᴴ) = (-Complex.I) • y.val
      simp [Matrix.conjTranspose_smul, y.property.1])
    (by rw [Matrix.trace_smul, y.property.2, smul_zero])
  left_inv x := by
    apply TracelessHermitian3.toMatrix_injective
    rw [TracelessHermitian3.toMatrix_ofMatrix]
    change (-Complex.I) • (Complex.I • TracelessHermitian3.toMatrix x) = _
    simp [smul_smul, Complex.I_mul_I]
  right_inv y := by
    apply Subtype.ext
    change Complex.I • TracelessHermitian3.toMatrix (TracelessHermitian3.ofMatrix ((-Complex.I) • y.val) _ _) = y.val
    rw [TracelessHermitian3.toMatrix_ofMatrix]
    simp [smul_smul, Complex.I_mul_I]
  map_add' x y := Subtype.ext (by
    change Complex.I • TracelessHermitian3.toMatrix (x + y) =
      Complex.I • TracelessHermitian3.toMatrix x + Complex.I • TracelessHermitian3.toMatrix y
    rw [map_add, smul_add])
  map_smul' r x := Subtype.ext (by
    change Complex.I • TracelessHermitian3.toMatrix (r • x) = r • (Complex.I • TracelessHermitian3.toMatrix x)
    rw [map_smul, smul_comm])

/-- In the trace-normalized complex model the full Casimir is the identity. -/
theorem complex_full_casimir_eq_id : operatorCasimir complexRestrictedOperatorAlgebra = LinearMap.id := by
  have hv : Module.finrank ℝ complexJordan.traceFree = 8 :=
    complexTraceEquiv.finrank_eq.trans fourPlane_dimension
  let F : complexOperatorAlgebra →ₗ[ℝ] SkewOperator complexJordan.traceFree :=
    (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap
  have hF : Function.Injective F := by
    intro x y h
    have h' : complexJordan.restrictDerivation ⟨x.val, complexOperatorAlgebra_le x.property⟩ =
        complexJordan.restrictDerivation ⟨y.val, complexOperatorAlgebra_le y.property⟩ := h
    exact Subtype.ext (congrArg (fun D : complexJordan.skewDerivations => D.val)
      (complexJordan.restrictDerivation_injective h'))
  have hk : Module.finrank ℝ complexRestrictedOperatorAlgebra = 8 := by
    change Module.finrank ℝ F.range = 8
    rw [LinearMap.finrank_range_of_inj hF, complexOperatorAlgebra,
      LinearMap.finrank_range_of_inj complexCommutatorLinear_injective,
      ← complexTraceToSkewEquiv.finrank_eq, fourPlane_dimension]
  rw [complex_full_casimir, hv, hk]
  norm_num

/-- Proposition 7-frames(a) on the actual complex commutator representation. -/
theorem complex_fixedSubalgebra_and_framePlane (T : Submodule ℝ (SkewOperator FullHermitian))
    (hT : T ≤ complexOperatorAlgebra) :
    fixedSpace T = (ℝ ∙ complexJordan.unit) ⊔
        (complexJordan.fixedTraceless T).map complexJordan.traceFree.subtype ∧
      complexJordan.unit ∈ fixedSpace T ∧
      (∀ x y, x ∈ fixedSpace T → y ∈ fixedSpace T → complexJordan.L x y ∈ fixedSpace T) ∧
      IsClosedPiece complexJordan.traceCubic (complexJordan.fixedTraceless T) ∧
      (Module.finrank ℝ (complexJordan.fixedTraceless T) = 2 →
        ∃ F : complexJordan.Frame, complexJordan.fixedTraceless T = F.plane complexJordan) :=
  complexJordan.fixedSubalgebra_and_framePlane complex_closedPlane_has_frame T
    (hT.trans complexOperatorAlgebra_le)

/-- The Cartan-plane theorem on the complex model for a full frame-type splitting. -/
theorem complex_operatorOD_fixedPlanes (T : Fin 4 → Submodule ℝ complexOperatorAlgebra)
    (hT : OrthogonalSplit (E := complexOperatorAlgebra) T)
    (htypes : ∀ i, IsFrameType ((T i).map
      (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap) 2 (1 / 3)) :
    OrthogonalSplit (E := complexJordan.traceFree)
      (fun i => complexJordan.fixedTraceless ((T i).map complexOperatorAlgebra.subtype)) ∧
      (∀ i, IsClosedPiece complexJordan.traceCubic
        (complexJordan.fixedTraceless ((T i).map complexOperatorAlgebra.subtype))) ∧
      ∃ F : Fin 4 → complexJordan.Frame,
        (∀ i, complexJordan.fixedTraceless ((T i).map complexOperatorAlgebra.subtype) =
          (F i).plane complexJordan) ∧
        ∀ i j, i ≠ j → ∀ a b, complexJordan.trace (complexJordan.L ((F i).point a) ((F j).point b)) = 1 / 3 := by
  have hc : operatorCasimir complexRestrictedOperatorAlgebra = (1 : ℝ) • LinearMap.id := by
    rw [one_smul, complex_full_casimir_eq_id]
  have hdim : 2 * Fintype.card (Fin 4) = Module.finrank ℝ complexJordan.traceFree := by
    rw [complexTraceEquiv.finrank_eq, fourPlane_dimension, Fintype.card_fin]
  exact complexJordan.operatorOD_fixedPlanes complexOperatorAlgebra complexOperatorAlgebra_le T hT
    2 (1 / 3) 1 (by norm_num) hc htypes hdim complex_closedPlane_has_frame

end

end ThirteenPlanes.Cartan
