module

public import ThirteenPlanes.Cartan.GradeRealAlbertCore
public import ThirteenPlanes.Cartan.GradeRealDescent
public import ThirteenPlanes.Cartan.AlbertDerivationComplexTrace
public import ThirteenPlanes.Cartan.AlbertGradingCharacters
public import ThirteenPlanes.Cartan.GradedRecutAction

@[expose] public section

set_option backward.privateInPublic true

/-! Real opposite-grade Cartans and their fixed planes for an arbitrary Albert grading. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading LieAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev G := LieComplex NativeAlbertDerivations

private theorem albertGradingRep_conjugation (D : G) (x : JC) :
    albertGradingRep (LieComplex.conjugation D) x =
      JC.conj (albertGradingRep D (JC.conj x)) := by
  change (albertDerivationComplexEquiv (LieComplex.conjugation D)).val x = _
  rw [albertDerivationComplexEquiv_conjugation, conjAlbertDerivation_apply]
  rfl

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)

/-- These degrees are the actual character eigenspaces for the native grading action. -/
theorem albertComplexGrade_mem_iff_character (γ : Charge) (D : G) :
    D ∈ albertComplexGrade hρ γ ↔
      ∀ s, (albertGradingActEquiv ρ s).conj (albertGradingRep D) =
        gradeCharacter s γ • albertGradingRep D := by
  change albertGradingRep D ∈ (albertGradingBasis hρ).derivationGrade γ ↔ _
  rw [albertGrading_derivationGrade_iff_character hρ]
  have hd : albertGradingRep D ∈ (albertGradingBasis hρ).derivations :=
    albertGradingRep_range hρ ▸ LinearMap.mem_range_self albertGradingRep D
  exact and_iff_right hd

private theorem albertComplexGrade_conjugate {γ : Charge} {D : G}
    (hd : D ∈ albertComplexGrade hρ γ) :
    LieComplex.conjugation D ∈ albertComplexGrade hρ (-γ) := by
  let M := albertGradingBasis hρ
  change albertGradingRep (LieComplex.conjugation D) ∈ M.derivationGrade (-γ)
  change albertGradingRep D ∈ M.derivationGrade γ at hd
  have hder : albertGradingRep (LieComplex.conjugation D) ∈ M.derivations :=
    albertGradingRep_range hρ ▸ LinearMap.mem_range_self albertGradingRep _
  refine ⟨hder, ?_⟩
  intro g
  obtain ⟨c, hc⟩ := (M.mem_derivationGrade.mp hd).2 (-g)
  refine ⟨star c, ?_⟩
  change albertGradingRep (LieComplex.conjugation D) ((albertGradingBasis hρ).basis g) =
    star c • (albertGradingBasis hρ).basis (g + -γ)
  rw [albertGradingRep_conjugation, albertGradingBasis_conj, hc, JC.conj_smul]
  change star c • JC.conj ((albertGradingBasis hρ).basis (-g + γ)) = _
  rw [albertGradingBasis_conj, show -(-g + γ) = g + -γ by abel]

/-- The compact real structure pairs each complex derivation degree nondegenerately
with its opposite for the trace of the native action. -/
theorem albertGrading_oppositeTraceNondegenerate :
    (albertGradingBasis hρ).OppositeTraceNondegenerate := by
  intro γ D hD hne
  have hD' : D ∈ albertGradingRep.range := by
    rw [albertGradingRep_range hρ]
    exact ((albertGradingBasis hρ).mem_derivationGrade.mp hD).1
  obtain ⟨X, rfl⟩ := hD'
  have hx : X ∈ albertComplexGrade hρ (-γ) := hD
  let E := albertDerivationComplexEquiv X
  have he : E ≠ 0 := by
    intro h
    apply hne
    exact congrArg (fun D : ComplexAlbertDerivations => D.val) h
  refine ⟨albertGradingRep (LieComplex.conjugation X), ?_, ?_⟩
  · change LieComplex.conjugation X ∈ albertComplexGrade hρ γ
    simpa only [neg_neg] using albertComplexGrade_conjugate hρ hx
  · have ht := complexAlbertDerivation_trace_conjugate_neg E he
    change (LinearMap.trace ℂ JC ((albertDerivationComplexEquiv X).val *
      (conjAlbertDerivation (albertDerivationComplexEquiv X)).val)).re < 0 at ht
    rw [← albertDerivationComplexEquiv_conjugation] at ht
    intro h0
    change (LinearMap.trace ℂ JC ((albertDerivationComplexEquiv X).val *
      (albertDerivationComplexEquiv (LieComplex.conjugation X)).val)) = 0 at h0
    rw [h0, Complex.zero_re] at ht
    exact lt_irrefl _ ht

private theorem albertComplexPair_commutative (p : SignedPlaneIndex) {X Y : G}
    (hx : X ∈ pairedGrade (albertComplexGrade hρ) p)
    (hy : Y ∈ pairedGrade (albertComplexGrade hρ) p) : ⁅X, Y⁆ = 0 := by
  let : Module.Finite ℂ JC := Module.Finite.of_basis (albertGradingBasis hρ).basis
  apply albertGradingRep_injective
  rw [map_zero, albertGradingRep_map_lie]
  exact (albertGradingBasis hρ).gradePair_commutative (albertGradingDerivations_finrank hρ)
    (albertGrading_oppositeTraceNondegenerate hρ) p.val.property
    ((albertComplexGradePair_mem hρ p X).mp hx) ((albertComplexGradePair_mem hρ p Y).mp hy)

/-- The actual sum of the two opposite grades, as a complex Lie subalgebra. -/
def albertGradingComplexPair (p : SignedPlaneIndex) : LieSubalgebra ℂ G :=
  { pairedGrade (albertComplexGrade hρ) p with
    lie_mem' := fun hx hy => (albertComplexPair_commutative hρ p hx hy).symm ▸
      (pairedGrade (albertComplexGrade hρ) p).zero_mem }

theorem albertGradingComplexPair_stable (p : SignedPlaneIndex) :
    Set.MapsTo LieComplex.conjugation
      (albertGradingComplexPair hρ p : Set G) (albertGradingComplexPair hρ p : Set G) := by
  intro X hX
  change X ∈ pairedGrade (albertComplexGrade hρ) p at hX
  obtain ⟨U, hU, V, hV, rfl⟩ := Submodule.mem_sup.mp hX
  have h1 := albertComplexGrade_conjugate hρ hU
  have h2 := albertComplexGrade_conjugate hρ hV
  rw [neg_neg] at h2
  change LieComplex.conjugation (U + V) ∈ pairedGrade (albertComplexGrade hρ) p
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, h2, _, h1, add_comm _ _⟩

theorem albertGradingComplexPair_selfCentralizing (p : SignedPlaneIndex) (X : G) :
    (∀ Y ∈ albertGradingComplexPair hρ p, ⁅X, Y⁆ = 0) ↔ X ∈ albertGradingComplexPair hρ p := by
  let : Module.Finite ℂ JC := Module.Finite.of_basis (albertGradingBasis hρ).basis
  constructor
  · intro h
    apply (albertComplexGradePair_mem hρ p X).mpr
    apply (albertGradingBasis hρ).mem_gradePair_of_centralizes
      (albertGradingDerivations_finrank hρ) p.val.property
    · exact albertGradingRep_range hρ ▸ LinearMap.mem_range_self albertGradingRep X
    · intro E hE
      rw [← albertComplexGradePair_map hρ p] at hE
      obtain ⟨Y, hY, rfl⟩ := hE
      rw [← albertGradingRep_map_lie, h Y hY, map_zero]
  · intro h Y hY
    exact albertComplexPair_commutative hρ p h hY

/-- The real Cartan is the intersection of the opposite complex grades with the compact form. -/
def albertGradingRealCartan (p : SignedPlaneIndex) : LieSubalgebra ℝ NativeAlbertDerivations :=
  LieComplex.descend (albertGradingComplexPair hρ p)

theorem albertGradingRealCartan_selfCentralizing (p : SignedPlaneIndex) :
    IsCompactCartan (albertGradingRealCartan hρ p) :=
  LieComplex.descend_selfCentralizing _ (albertGradingComplexPair_stable hρ p)
    (albertGradingComplexPair_selfCentralizing hρ p)

theorem albertGradingRealCartan_finrank (p : SignedPlaneIndex) :
    Module.finrank ℝ (albertGradingRealCartan hρ p) = 4 :=
  (LieComplex.descend_finrank_eq_of_stable _ (albertGradingComplexPair_stable hρ p)).trans
    (albertComplexGradePair_finrank hρ p)

theorem albertGradingRealCartans_isInternal :
    DirectSum.IsInternal (fun p => (albertGradingRealCartan hρ p).toSubmodule) := by
  apply LieComplex.descend_isInternal_of_stable _ (albertGradingComplexPair_stable hρ)
  exact pairedGrade_isInternal _ (albertComplexGrades_isInternal hρ) (albertComplexGrade_zero hρ)

theorem albertGradingRealCartans_killing_orthogonal :
    Pairwise fun p q : SignedPlaneIndex =>
      ∀ X ∈ albertGradingRealCartan hρ p, ∀ Y ∈ albertGradingRealCartan hρ q,
      killingForm ℝ NativeAlbertDerivations X Y = 0 :=
  LieComplex.killing_orthogonal_descend (albertGradingComplexPair hρ)
    (albertComplexGradePairs_killing_orthogonal hρ)

/-- The common nullspace of the descended Cartan is the labelled graded plane. -/
theorem albertGradingRealCartan_fixedPlane (p : SignedPlaneIndex) :
    albertRealFixed (albertGradingRealCartan hρ p) = pointPlane ρ p := by
  let M := albertGradingBasis hρ
  let : Module.Finite ℂ JC := Module.Finite.of_basis M.basis
  let H := albertGradingComplexPair hρ p
  ext x
  rw [mem_albertRealFixed, ← albertGrading_of_mem_pointAxis_iff hρ p x,
    M.mem_gradeAxis_iff_fixed (albertGradingDerivations_finrank hρ) p.val.property]
  constructor
  · intro hx D hD
    rw [← albertComplexGradePair_map hρ p] at hD
    obtain ⟨X, hX, rfl⟩ := hD
    have hX' : X ∈ LieComplex.extend (LieComplex.descend H) := by
      rw [LieComplex.extend_descend_of_stable H (albertGradingComplexPair_stable hρ p)]
      exact hX
    obtain ⟨hr, hi⟩ := (LieComplex.mem_extend _ _).mp hX'
    rw [← LieComplex.decompose_smul X, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      albertGradingRep_ofReal, albertGradingRep_ofReal, hx _ hr, hx _ hi, JC.of_zero, smul_zero, add_zero]
  · intro hx D hD
    have hD' : LieComplex.ofReal D ∈ pairedGrade (albertComplexGrade hρ) p := hD
    have he := hx (albertGradingRep (LieComplex.ofReal D))
      ((albertComplexGradePair_mem hρ p _).mp hD')
    rw [albertGradingRep_ofReal, ← JC.of_zero] at he
    exact JC.of_injective he

end

end ThirteenPlanes.Cartan
