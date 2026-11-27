module

public import ThirteenPlanes.Cartan.LieCompactConjugation
public import ThirteenPlanes.Cartan.F4.Corollaries
public import Mathlib.Algebra.Lie.BaseChange

@[expose] public section

set_option backward.privateInPublic true

/-! Real Lie identification with the compact real form of the Chevalley algebra. -/

namespace ThirteenPlanes.Cartan

noncomputable section

namespace LieConjugation

variable {G : Type*} [LieRing G] [LieAlgebra ℂ G]

/-- The real Lie algebra of points fixed by a conjugation of a complex Lie algebra. -/
def fixedRealLie (σ : LieConjugation G) : LieSubalgebra ℝ (RestrictScalars ℝ ℂ G) := by
  let f := RestrictScalars.addEquiv ℝ ℂ G
  refine
    { carrier := {x | σ (f x) = f x}
      add_mem' := ?_
      zero_mem' := ?_
      smul_mem' := ?_
      lie_mem' := ?_ }
  · intro x y hx hy
    change σ (f x) = f x at hx
    change σ (f y) = f y at hy
    change σ (f (x + y)) = f (x + y)
    rw [map_add, σ.add, hx, hy]
  · change σ (f 0) = f 0
    rw [map_zero]
    simpa only [zero_smul, star_zero] using σ.smul 0 (0 : G)
  · intro r x hx
    change σ (f x) = f x at hx
    change σ (f (r • x)) = f (r • x)
    have hr : f (r • x) = (r : ℂ) • f x := rfl
    rw [hr, σ.smul, Complex.star_def, Complex.conj_ofReal, hx]
  · intro x y hx hy
    change σ (f x) = f x at hx
    change σ (f y) = f y at hy
    change σ (f ⁅x, y⁆) = f ⁅x, y⁆
    have hlie : f ⁅x, y⁆ = ⁅f x, f y⁆ := rfl
    rw [hlie, σ.bracket, hx, hy]

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K]

private theorem ofReal_realPart_of_fixed (z : LieComplex K)
    (hz : LieComplex.compactConjugation z = z) :
    LieComplex.ofReal (LieComplex.realPart z) = z := by
  have hi := congrArg LieComplex.imagPart hz
  rw [LieComplex.compactConjugation_apply, LieComplex.imagPart_conjugation] at hi
  have htwo : (2 : ℝ) • LieComplex.imagPart z = 0 := by
    calc
      _ = LieComplex.imagPart z + LieComplex.imagPart z := two_smul ℝ _
      _ = LieComplex.imagPart z + (-LieComplex.imagPart z) :=
        congrArg (fun x => LieComplex.imagPart z + x) hi.symm
      _ = 0 := add_neg_cancel _
  have hzero := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa only [hzero, map_zero, smul_zero, add_zero] using LieComplex.decompose_smul z

/-- A complex Lie equivalence intertwining conjugations restricts to the real fixed algebras. -/
def realLieEquivOfIntertwining (e : LieComplex K ≃ₗ⁅ℂ⁆ G) (σ : LieConjugation G)
    (h : ∀ z, e (LieComplex.compactConjugation z) = σ (e z)) :
    K ≃ₗ⁅ℝ⁆ σ.fixedRealLie := by
  let f : K →ₗ⁅ℝ⁆ σ.fixedRealLie :=
    { toFun := fun x => ⟨e (LieComplex.ofReal x), by
        change σ (e (LieComplex.ofReal x)) = e (LieComplex.ofReal x)
        rw [← h, LieComplex.compactConjugation_apply, LieComplex.conjugation_ofReal]⟩
      map_add' := fun x y => Subtype.ext (by
        change e (LieComplex.ofReal (x + y)) = e (LieComplex.ofReal x) + e (LieComplex.ofReal y)
        rw [map_add, map_add])
      map_smul' := fun r x => Subtype.ext (by
        change e (LieComplex.ofReal (r • x)) = (r : ℂ) • e (LieComplex.ofReal x)
        rw [map_smul, ← algebraMap_smul ℂ r, map_smul]
        rfl)
      map_lie' := by
        intro x y
        apply Subtype.ext
        change e (LieComplex.ofReal ⁅x, y⁆) = ⁅e (LieComplex.ofReal x), e (LieComplex.ofReal y)⁆
        rw [LieHom.map_lie, LieEquiv.map_lie] }
  refine LieEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    exact LieComplex.ofReal_injective (e.injective (congrArg Subtype.val hxy))
  · intro y
    let z := e.symm y.val
    have hz : e z = y.val := e.apply_symm_apply _
    have hy : σ y.val = y.val := y.property
    have hfix : LieComplex.compactConjugation z = z :=
      e.injective ((h z).trans ((congrArg σ.toFun hz).trans (hy.trans hz.symm)))
    refine ⟨LieComplex.realPart z, Subtype.ext ?_⟩
    change e (LieComplex.ofReal (LieComplex.realPart z)) = y.val
    rw [ofReal_realPart_of_fixed z hfix, hz]

/-- Every compact conjugation on a complexification has fixed algebra real-isomorphic
to the original compact real Lie algebra. -/
theorem nonempty_realLieEquiv_fixed [Module.Finite ℝ K] (hK : CompactKilling K)
    (e : LieComplex K ≃ₗ⁅ℂ⁆ G) (σ : LieConjugation G) (hσ : σ.IsCompact) :
    Nonempty (K ≃ₗ⁅ℝ⁆ σ.fixedRealLie) := by
  let τ : LieConjugation (LieComplex K) := LieComplex.compactConjugation
  let σ' := σ.transport e.symm
  have hσ' : σ'.IsCompact := transport_compact e.symm σ hσ
  obtain ⟨a, ha⟩ := τ.exists_intertwining_aut σ'
    (LieComplex.compactConjugation_isCompact hK) hσ'
    LieComplex.killing_conjugation_conjugation
  refine ⟨realLieEquivOfIntertwining (a.symm.trans e) σ ?_⟩
  intro z
  have hint : σ' (a.symm z) = a.symm (τ z) := by
    apply a.injective
    exact (ha (a.symm z)).trans
      ((congrArg τ.toFun (a.apply_symm_apply z)).trans (a.apply_symm_apply (τ z)).symm)
  change e (a.symm (τ z)) = σ (e (a.symm z))
  rw [← hint]
  simp [σ']

end LieConjugation

/-- A compact real model of the Chevalley E₆ algebra, chosen from the compact conjugations
of that algebra itself. Its argument is a proof of existence. -/
def compactChevalleyE6 (h : ∃ σ : LieConjugation (LieAlgebra.e₆ ℂ), σ.IsCompact) :
    LieSubalgebra ℝ (RestrictScalars ℝ ℂ (LieAlgebra.e₆ ℂ)) :=
  (Classical.choose h).fixedRealLie

theorem compactChevalleyE6_proof_irrel
    (h h' : ∃ σ : LieConjugation (LieAlgebra.e₆ ℂ), σ.IsCompact) :
    compactChevalleyE6 h = compactChevalleyE6 h' := rfl

namespace SecondRowMagicSquareInput

/-- The same Tits input as the second-row corollary supplies existence of a compact
conjugation on the Chevalley algebra. -/
theorem exists_compactChevalleyE6_conjugation (magic : SecondRowMagicSquareInput) :
    ∃ σ : LieConjugation (LieAlgebra.e₆ ℂ), σ.IsCompact := by
  let H := magic.albertRealization
  let : Module.Finite ℝ H.operators :=
    Module.Finite.of_surjective H.coordinates.toLinearMap H.coordinates.surjective
  obtain ⟨e⟩ := magic.albert_type
  exact ⟨LieComplex.compactConjugation.transport e,
    LieConjugation.transport_compact e _
      (LieComplex.compactConjugation_isCompact H.compact)⟩

/-- The octonionic second row is real-isomorphic to the fixed algebra of every compact
conjugation of the Chevalley E₆ algebra. -/
theorem albert_realEquiv_fixedChevalleyE6 (magic : SecondRowMagicSquareInput)
    (σ : LieConjugation (LieAlgebra.e₆ ℂ)) (hσ : σ.IsCompact) :
    Nonempty (magic.albertRealization.operators ≃ₗ⁅ℝ⁆ σ.fixedRealLie) := by
  let H := magic.albertRealization
  let : Module.Finite ℝ H.operators :=
    Module.Finite.of_surjective H.coordinates.toLinearMap H.coordinates.surjective
  obtain ⟨e⟩ := magic.albert_type
  exact LieConjugation.nonempty_realLieEquiv_fixed H.compact e σ hσ

/-- The octonionic second row is real-isomorphic to the compact real form of the Chevalley
E₆ algebra. The existence needed in the target follows from the same Tits input. -/
theorem albert_real_type (magic : SecondRowMagicSquareInput) :
    Nonempty (magic.albertRealization.operators ≃ₗ⁅ℝ⁆
      compactChevalleyE6 magic.exists_compactChevalleyE6_conjugation) :=
  magic.albert_realEquiv_fixedChevalleyE6 _
    (Classical.choose_spec magic.exists_compactChevalleyE6_conjugation)

/-- The chosen compact Chevalley model has negative definite real Killing form. -/
theorem compactChevalleyE6_compactKilling (magic : SecondRowMagicSquareInput) :
    CompactKilling (compactChevalleyE6 magic.exists_compactChevalleyE6_conjugation) := by
  obtain ⟨e⟩ := magic.albert_real_type
  intro x hx
  have hn : e.symm x ≠ 0 := fun h =>
    hx (e.symm.injective (h.trans (map_zero e.symm).symm))
  rw [← LieAlgebra.killingForm_of_equiv_apply e.symm]
  exact magic.albertRealization.compact _ hn

end SecondRowMagicSquareInput

/-- The second-row corollary with the octonionic type given by a real Lie equivalence. -/
theorem compactSecondRowCorollary_realE6_ofMagicSquare (magic : SecondRowMagicSquareInput)
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Nonempty (magic.complexRealization.operators ≃ₗ⁅ℝ⁆ (secondRowCompactSU 3 × secondRowCompactSU 3)) ∧
    Nonempty (magic.quaternionRealization.operators ≃ₗ⁅ℝ⁆ secondRowCompactSU 6) ∧
    Nonempty (magic.albertRealization.operators ≃ₗ⁅ℝ⁆
      compactChevalleyE6 magic.exists_compactChevalleyE6_conjugation) ∧
    SecondRowLieCase magic.complexRealization 2 ι ∧
    SecondRowLieCase magic.quaternionRealization 3 ι ∧
    SecondRowLieCase magic.albertRealization 4 ι := by
  obtain ⟨hc, hh, _, c, h, o⟩ := compactSecondRowCorollary_ofMagicSquare magic ι
  exact ⟨hc, hh, magic.albert_real_type, c, h, o⟩

end
end ThirteenPlanes.Cartan
