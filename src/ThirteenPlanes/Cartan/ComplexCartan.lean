module

public import ThirteenPlanes.Cartan.ComplexCasimir
public import ThirteenPlanes.Cartan.ComplexDiagonalization
public import ThirteenPlanes.Cartan.DiagonalWeightsComplex

@[expose] public section

set_option backward.privateInPublic true

/-! Fixed planes of the actual compact complex Cartans. -/

namespace ThirteenPlanes.Cartan

open RoundCubics
open scoped Matrix

noncomputable section

/-- A maximal commutative subspace of the represented compact complex Lie algebra. -/
def IsComplexOperatorCartan (T : Submodule ℝ complexOperatorAlgebra) : Prop :=
  (∀ A B : T, Commute A.val.val.val B.val.val.val) ∧
    ∀ D : complexOperatorAlgebra, (∀ H : T, Commute D.val.val H.val.val.val) → D ∈ T

private def complexMatrixBracket (A B : complexSkewTracelessMatrices) :
    complexSkewTracelessMatrices := ⟨A.val * B.val - B.val * A.val, by
  change (A.val * B.val - B.val * A.val)ᴴ = -(A.val * B.val - B.val * A.val) ∧
    Matrix.trace (A.val * B.val - B.val * A.val) = 0
  constructor
  · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, A.property.1, B.property.1,
      neg_mul_neg, neg_sub]
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]⟩

private theorem complexCommutatorBrackets (A B : complexSkewTracelessMatrices) :
    complexCommutator (complexMatrixBracket A B) =
      complexCommutator A * complexCommutator B - complexCommutator B * complexCommutator A := by
  apply LinearMap.ext
  intro x
  apply fullMatrix_injective
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, map_sub, complexCommutator_matrix]
  change (A.val * B.val - B.val * A.val) * fullMatrix x -
        fullMatrix x * (A.val * B.val - B.val * A.val) = _
  noncomm_ring

private theorem complexCommutator_commute_iff (A B : complexSkewTracelessMatrices) :
    Commute (complexCommutator A) (complexCommutator B) ↔ Commute A.val B.val := by
  constructor
  · intro h
    have hb : complexCommutatorLinear (complexMatrixBracket A B) = 0 := by
      apply Subtype.ext
      change complexCommutator (complexMatrixBracket A B) = 0
      rw [complexCommutatorBrackets, h.eq, sub_self]
    have hz : complexMatrixBracket A B = 0 :=
      complexCommutatorLinear_injective (hb.trans (complexCommutatorLinear.map_zero).symm)
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  · intro h
    have hb : complexMatrixBracket A B = 0 := Subtype.ext (sub_eq_zero.mpr h.eq)
    have hz : complexCommutator (complexMatrixBracket A B) = 0 := by
      rw [hb]
      exact congrArg Subtype.val complexCommutatorLinear.map_zero
    rw [complexCommutatorBrackets] at hz
    exact sub_eq_zero.mp hz

private def complexCommutatorEquiv : complexSkewTracelessMatrices ≃ₗ[ℝ] complexOperatorAlgebra :=
  LinearEquiv.ofInjective complexCommutatorLinear complexCommutatorLinear_injective

private theorem complexEquiv_symm_commutator (D : complexOperatorAlgebra) :
    complexCommutator (complexCommutatorEquiv.symm D) = D.val.val :=
  congrArg (fun E : complexOperatorAlgebra => E.val.val)
    (complexCommutatorEquiv.apply_symm_apply D)

private theorem complexDiagonal_commute (a b : complexCartanParameters) :
    Commute (complexSkewDiagonal a).val (complexSkewDiagonal b).val := by
  show (complexSkewDiagonal a).val * (complexSkewDiagonal b).val =
    (complexSkewDiagonal b).val * (complexSkewDiagonal a).val
  simp only [complexSkewDiagonal_matrix, Matrix.diagonal_mul_diagonal, mul_comm]

/-- The actual standard complex torus is maximal commutative. -/
theorem complexStandardCartan_isCartan : IsComplexOperatorCartan complexStandardCartan := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact (complexCommutator_commute_iff _ _).mpr (complexDiagonal_commute a b)
  · intro D hD
    let A := complexCommutatorEquiv.symm D
    have hA : ∀ a : complexCartanParameters, Commute A.val (complexSkewDiagonal a).val := by
      intro a
      apply (complexCommutator_commute_iff A (complexSkewDiagonal a)).mp
      rw [complexEquiv_symm_commutator]
      exact hD ⟨complexStandardFull a, ⟨a, rfl⟩⟩
    obtain ⟨a, ha⟩ := complexSkewDiagonal_centralizer A hA
    exact ⟨a, (congrArg complexCommutatorEquiv ha).trans
      (complexCommutatorEquiv.apply_symm_apply D)⟩

private abbrev restrictComplex := complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le

private theorem complexRestrictedCommutator_equiv (A : complexSkewTracelessMatrices) :
    complexRestrictedCommutator A = restrictComplex (complexCommutatorEquiv A) := rfl

private theorem complexConjugatedSkew_roundtrip (U : ComplexUnitary3)
    (A : complexSkewTracelessMatrices) :
    complexConjugatedSkew U (complexConjugatedSkew (star U) A) = A := by
  apply Subtype.ext
  change complexMatrixAd U (complexMatrixAd (star U) A.val) = A.val
  have h := complexMatrixAd_inv (star U) A.val
  simpa only [star_star] using h

/-- One actual special-unitary conjugation sends the whole compact Cartan to the standard one. -/
/- This proves compact Cartan conjugacy in the complex three-by-three matrix model
by simultaneous diagonalization of commuting skew-Hermitian operators. For the
general compact conjugacy theorem cited in the paper, see Anthony Knapp, Structure
Theory of Semisimple Lie Groups (1997), Theorem 3.6, p. 16. -/
theorem complexOperatorCartan_conjugateStandard (T : Submodule ℝ complexOperatorAlgebra)
    (hT : IsComplexOperatorCartan T) :
    ∃ U : ComplexSpecialUnitary3, (T.map restrictComplex.toLinearMap).map
      (conjugateSkew ((complexSU3Action U).traceAction complexJordan)).toLinearMap =
        complexStandardCartan.map restrictComplex.toLinearMap := by
  let A (D : T) := complexCommutatorEquiv.symm D.val
  have hA (D E : T) : Commute (A D).val (A E).val := by
    apply (complexCommutator_commute_iff (A D) (A E)).mp
    change Commute (complexCommutator (complexCommutatorEquiv.symm D.val))
      (complexCommutator (complexCommutatorEquiv.symm E.val))
    rw [complexEquiv_symm_commutator, complexEquiv_symm_commutator]
    exact hT.1 D E
  obtain ⟨U, hU⟩ := complexSkew_simultaneousDiagonalization A (fun D E _ => hA D E)
  let G : ComplexUnitary3 := ⟨U.val, U.property.1⟩
  have hd (D : T) : ∃ a : complexCartanParameters,
      complexConjugatedSkew G (A D) = complexSkewDiagonal a := by
    obtain ⟨a, hsum, ha⟩ := hU D
    let w : complexCartanParameters := ⟨a, hsum⟩
    exact ⟨w, Subtype.ext (ha.trans (complexSkewDiagonal_matrix w).symm)⟩
  have htransport (D : complexOperatorAlgebra) :
      conjugateSkew ((complexSU3Action U).traceAction complexJordan) (restrictComplex D) =
        complexRestrictedCommutator (complexConjugatedSkew G (complexCommutatorEquiv.symm D)) := by
    change conjugateSkew ((complexUnitaryAction G).traceAction complexJordan) (restrictComplex D) = _
    have he := complex_conjugate_restrictedCommutator G (complexCommutatorEquiv.symm D)
    simpa only [complexRestrictedCommutator_equiv, complexCommutatorEquiv.apply_symm_apply] using he
  refine ⟨U, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨D, hD, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := hd ⟨D, hD⟩
    refine ⟨complexStandardFull a, ⟨a, rfl⟩, ?_⟩
    have he := htransport D
    change complexConjugatedSkew G (complexCommutatorEquiv.symm D) = complexSkewDiagonal a at ha
    rw [ha] at he
    exact he.symm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    let X := complexConjugatedSkew (star G) (complexSkewDiagonal a)
    let D := complexCommutatorEquiv X
    have hD : D ∈ T := by
      apply hT.2
      intro H
      change Commute (complexCommutator X) H.val.val.val
      rw [← complexEquiv_symm_commutator H.val]
      apply (complexCommutator_commute_iff X (A H)).mpr
      obtain ⟨b, hb⟩ := hd H
      have hx : complexMatrixAd G X.val = (complexSkewDiagonal a).val :=
        congrArg Subtype.val (complexConjugatedSkew_roundtrip G (complexSkewDiagonal a))
      have hy : complexMatrixAd G (A H).val = (complexSkewDiagonal b).val :=
        congrArg Subtype.val hb
      show X.val * (A H).val = (A H).val * X.val
      apply (complexMatrixAd G).injective
      change complexMatrixAd G (X.val * (A H).val) = complexMatrixAd G ((A H).val * X.val)
      calc
        _ = complexMatrixAd G X.val * complexMatrixAd G (A H).val := map_mul _ _ _
        _ = complexMatrixAd G (A H).val * complexMatrixAd G X.val := by
          rw [hx, hy, (complexDiagonal_commute a b).eq]
        _ = _ := (map_mul (complexMatrixAd G) _ _).symm
    refine ⟨restrictComplex D, ⟨D, hD, rfl⟩, ?_⟩
    have he := htransport D
    change _ = complexRestrictedCommutator
      (complexConjugatedSkew G (complexCommutatorEquiv.symm (complexCommutatorEquiv X))) at he
    rw [complexCommutatorEquiv.symm_apply_apply] at he
    rw [show complexConjugatedSkew G X = complexSkewDiagonal a from
      complexConjugatedSkew_roundtrip G _] at he
    exact he

/-- Every compact complex Cartan has rank two and frame type constant one third. -/
theorem complexOperatorCartan_frameType (T : Submodule ℝ complexOperatorAlgebra)
    (hT : IsComplexOperatorCartan T) :
    IsFrameType (T.map restrictComplex.toLinearMap) 2 (1 / 3) := by
  obtain ⟨U, hU⟩ := complexOperatorCartan_conjugateStandard T hT
  let g := (complexSU3Action U).traceAction complexJordan
  have h := (conjugate_frameType_fixed g.symm _ complexStandardFrameType).1
  rw [← hU, conjugateSkew_map_roundtrip] at h
  exact h

/-- The four fixed planes of a compact complex Cartan decomposition are unbiased frame planes. -/
theorem complex_cartanOD_fixedPlanes (T : Fin 4 → Submodule ℝ complexOperatorAlgebra)
    (hT : OrthogonalSplit (E := complexOperatorAlgebra) T) (hCartan : ∀ i, IsComplexOperatorCartan (T i)) :
    OrthogonalSplit (E := complexJordan.traceFree)
      (fun i => complexJordan.fixedTraceless ((T i).map complexOperatorAlgebra.subtype)) ∧
      (∀ i, IsClosedPiece complexJordan.traceCubic
        (complexJordan.fixedTraceless ((T i).map complexOperatorAlgebra.subtype))) ∧
      ∃ F : Fin 4 → complexJordan.Frame,
        (∀ i, complexJordan.fixedTraceless ((T i).map complexOperatorAlgebra.subtype) =
          (F i).plane complexJordan) ∧
        ∀ i j, i ≠ j → ∀ a b, complexJordan.trace (complexJordan.L ((F i).point a) ((F j).point b)) = 1 / 3 :=
  complex_operatorOD_fixedPlanes T hT (fun i => complexOperatorCartan_frameType (T i) (hCartan i))

end

end ThirteenPlanes.Cartan
