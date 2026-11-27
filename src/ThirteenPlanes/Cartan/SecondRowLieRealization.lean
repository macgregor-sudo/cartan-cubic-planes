module

public import ThirteenPlanes.Cartan.SecondRowNativeCartans
public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition
public import Mathlib.Algebra.Lie.SerreConstruction
public import Mathlib.Algebra.Lie.Prod

@[expose] public section

/-! The quoted compact Lie identifications use the actual second-row commutators. -/

namespace ThirteenPlanes.Cartan

open scoped Matrix

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

section Associative

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Inside a compact operator Lie algebra, self-centralizing commuting spaces are Lie Cartans. -/
theorem isOperatorCartanFor_iff_lieCartan (S : LieSubalgebra ℝ A) [Module.Finite ℝ S]
    (hS : CompactKilling S) (C : LieSubalgebra ℝ S) :
    IsOperatorCartanFor S.toSubmodule.subtype C.toSubmodule ↔ C.IsCartanSubalgebra := by
  rw [← compactCartan_iff_cartan hS]
  have hzero (x y : S) : Commute x.val y.val ↔ ⁅x, y⁆ = 0 := by
    constructor
    · intro h
      exact Subtype.ext (sub_eq_zero.mpr h.eq)
    · intro h
      exact sub_eq_zero.mp (congrArg Subtype.val h)
  constructor
  · intro hc x
    exact ⟨fun h => (hc x).mp (fun y => (hzero x y).mpr (h y y.property)),
      fun h y hy => (hzero x y).mp (((hc x).mpr h) ⟨y, hy⟩)⟩
  · intro hc x
    exact ⟨fun h => (hc x).mp (fun y hy => (hzero x y).mp (h ⟨y, hy⟩)),
      fun h y => (hzero x y).mpr (((hc x).mpr h) y y.property)⟩

end Associative

/-- The compact Lie algebra of traceless skew-Hermitian matrices with the matrix commutator. -/
def secondRowCompactSU (n : ℕ) : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | Aᴴ = -A ∧ Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro A B ⟨hA, tA⟩ ⟨hB, tB⟩
    exact ⟨by rw [Matrix.conjTranspose_add, hA, hB, neg_add],
      by rw [Matrix.trace_add, tA, tB, add_zero]⟩
  smul_mem' := by
    rintro r A ⟨hA, tA⟩
    exact ⟨by rw [Matrix.conjTranspose_smul, star_trivial, hA, smul_neg],
      by rw [Matrix.trace_smul, tA, smul_zero]⟩
  lie_mem' := by
    rintro A B ⟨hA, _⟩ ⟨hB, _⟩
    change (A * B - B * A)ᴴ = -(A * B - B * A) ∧ Matrix.trace (A * B - B * A) = 0
    constructor
    · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA, hB,
        neg_mul_neg, neg_sub]
    · rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- The actual second-row operators are closed under commutators and have compact Killing form.
These are the real operator and compactness clauses of the quoted identification. -/
structure SecondRowCompactRealization (M : TraceJordanData J)
    (K : Submodule ℝ (SkewOperator J)) where
  operators : LieSubalgebra ℝ (Module.End ℂ (Complexified J))
  carrier_eq : operators.toSubmodule = secondRowSpace M K
  compact : CompactKilling operators

/-- The quoted second row of the compact magic square. The compact simple types are
A2 (su(3)), A5 (su(6)), and E6, whose complexification is the Chevalley–Serre algebra. -/
/- The input packages the type identifications of Jacques Tits's compact magic square.
See Baez, The Octonions, §4.3, Table 5, and Chevalley–Schafer (1950). For the
commutator derivations in the construction see Schafer (1966) and Yokota,
Exceptional Lie Groups, Proposition 2.4.1(2). The Albert input identifies the
complexification. The real compact E₆ identification is proved downstream. -/
structure SecondRowMagicSquareInput where
  complexRealization : SecondRowCompactRealization complexJordan complexOperatorAlgebra
  quaternionRealization : SecondRowCompactRealization quaternionJordan quaternionOperatorAlgebra
  albertRealization : SecondRowCompactRealization albertJordan albertJordan.skewDerivations
  complex_type : Nonempty
    (complexRealization.operators ≃ₗ⁅ℝ⁆ (secondRowCompactSU 3 × secondRowCompactSU 3))
  quaternion_type : Nonempty
    (quaternionRealization.operators ≃ₗ⁅ℝ⁆ secondRowCompactSU 6)
  albert_type : Nonempty (LieComplex albertRealization.operators ≃ₗ⁅ℂ⁆ LieAlgebra.e₆ ℂ)
  complex_factor_simple : LieAlgebra.IsSimple ℝ (secondRowCompactSU 3)
  quaternion_simple : LieAlgebra.IsSimple ℝ quaternionRealization.operators
  albert_simple : LieAlgebra.IsSimple ℝ albertRealization.operators

namespace SecondRowCompactRealization

variable {M : TraceJordanData J} {K : Submodule ℝ (SkewOperator J)}
  (H : SecondRowCompactRealization M K)

/-- The linear map identifies the same literal operators with their Lie-algebra carrier. -/
def coordinates : secondRowSpace M K ≃ₗ[ℝ] H.operators :=
  LinearEquiv.ofEq _ _ H.carrier_eq.symm

@[simp] theorem coordinates_apply (X : secondRowSpace M K) : (H.coordinates X).val = X.val := rfl

/-- Complex conjugation in the same coordinates on the quoted Lie algebra. -/
def theta : H.operators ≃ₗ[ℝ] H.operators :=
  H.coordinates.symm.trans ((secondRowTheta M K).trans H.coordinates)

@[simp] theorem theta_coordinates (X : secondRowSpace M K) :
    H.theta (H.coordinates X) = H.coordinates (secondRowTheta M K X) := by
  simp only [theta, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The commutative extension as a Lie subalgebra carrying the literal operator bracket. -/
def liftCartan (T : Submodule ℝ K) {rank : ℕ} (h : SecondRowCartanExtension M K T rank) :
    LieSubalgebra ℝ H.operators where
  toSubmodule := (secondRowPieceInSpace M T).map H.coordinates.toLinearMap
  lie_mem' := by
    rintro _ _ ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
    have hc := h.commutes ⟨X, hX⟩ ⟨Y, hY⟩
    have hz : ⁅H.coordinates X, H.coordinates Y⁆ = 0 :=
      Subtype.ext (sub_eq_zero.mpr hc.eq)
    change ⁅H.coordinates X, H.coordinates Y⁆ ∈
      (secondRowPieceInSpace M T).map H.coordinates.toLinearMap
    rw [hz]
    exact Submodule.zero_mem _

variable [FiniteDimensional ℝ J]

/-- Pulling back a Cartan in the quoted compact Lie algebra gives exactly the intrinsic
maximal commuting subspace of the same complex operators. -/
theorem operatorCartan_iff (C : LieSubalgebra ℝ H.operators) :
    IsSecondRowOperatorCartan M K (C.toSubmodule.comap H.coordinates.toLinearMap) ↔
      C.IsCartanSubalgebra := by
  let : Module.Finite ℝ H.operators := Module.Finite.of_surjective
    H.coordinates.toLinearMap H.coordinates.surjective
  rw [← isOperatorCartanFor_iff_lieCartan H.operators H.compact]
  constructor
  · intro h x
    obtain ⟨X, rfl⟩ := H.coordinates.surjective x
    constructor
    · intro hx
      apply (h X).mp
      rintro ⟨Y, hY⟩
      exact hx ⟨H.coordinates Y, hY⟩
    · intro hx
      rintro ⟨Y, hY⟩
      obtain ⟨Y₀, rfl⟩ := H.coordinates.surjective Y
      exact ((h X).mpr hx) ⟨Y₀, hY⟩
  · intro h x
    constructor
    · intro hx
      apply (h (H.coordinates x)).mp
      rintro ⟨Y, hY⟩
      obtain ⟨Y₀, rfl⟩ := H.coordinates.surjective Y
      exact hx ⟨Y₀, hY⟩
    · intro hx
      rintro ⟨Y, hY⟩
      exact ((h (H.coordinates x)).mpr hx) ⟨H.coordinates Y, hY⟩

/-- The lifted Lie Cartan is stable by conjugation, has dimension `rank + 2`, and is the
unique Lie Cartan containing the original real Cartan. -/
theorem liftCartan_spec (T : Submodule ℝ K) {rank : ℕ} (h : SecondRowCartanExtension M K T rank) :
    (H.liftCartan T h).IsCartanSubalgebra ∧
    Module.finrank ℝ (H.liftCartan T h) = rank + 2 ∧
    (H.liftCartan T h).toSubmodule.map H.theta.toLinearMap = (H.liftCartan T h).toSubmodule ∧
    (∀ X : T, H.coordinates (secondRowRealInclusion M K X.val) ∈ H.liftCartan T h) ∧
    ∀ C : LieSubalgebra ℝ H.operators, C.IsCartanSubalgebra →
      (∀ X : T, H.coordinates (secondRowRealInclusion M K X.val) ∈ C) →
      C = H.liftCartan T h := by
  let P := secondRowPieceInSpace M T
  have he : (H.liftCartan T h).toSubmodule =
      (secondRowPieceInSpace M T).map H.coordinates.toLinearMap := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (H.operatorCartan_iff _).mp
    rw [he, Submodule.comap_map_eq_of_injective H.coordinates.injective]
    exact h.isCartan
  · change Module.finrank ℝ (P.map H.coordinates.toLinearMap) = _
    exact ((H.coordinates.submoduleMap P).finrank_eq.symm).trans h.finrank_eq
  · rw [he, ← Submodule.map_comp]
    have hmap : H.theta.toLinearMap.comp H.coordinates.toLinearMap =
        H.coordinates.toLinearMap.comp (secondRowTheta M K).toLinearMap := by
      apply LinearMap.ext
      exact H.theta_coordinates
    rw [hmap, Submodule.map_comp, h.stable]
  · intro X
    exact Submodule.mem_map_of_mem (secondRowRealInclusion_mem_piece M T X)
  · intro C hC hContains
    have hop := (H.operatorCartan_iff C).mpr hC
    have hp := h.unique (C.toSubmodule.comap H.coordinates.toLinearMap) hop hContains
    apply LieSubalgebra.toSubmodule_injective
    rw [he, ← hp, Submodule.map_comap_eq_of_surjective H.coordinates.surjective]

/-- The common dimension of any compact Lie Cartans follows from that of a constructed lift.
The uniformity premise is the equal-dimension consequence of compact Cartan conjugacy. -/
theorem ambient_rank_of_conjugacy
    (uniform : ∀ C D : LieSubalgebra ℝ H.operators, C.IsCartanSubalgebra →
      D.IsCartanSubalgebra → Module.finrank ℝ C = Module.finrank ℝ D)
    (T : Submodule ℝ K) {rank : ℕ} (h : SecondRowCartanExtension M K T rank)
    (C : LieSubalgebra ℝ H.operators) (hC : C.IsCartanSubalgebra) :
    Module.finrank ℝ C = rank + 2 := by
  have lift := H.liftCartan_spec T h
  exact (uniform C (H.liftCartan T h) hC lift.1).trans lift.2.1

end SecondRowCompactRealization

end
end ThirteenPlanes.Cartan
