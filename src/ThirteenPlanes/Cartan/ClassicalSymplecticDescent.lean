module

public import ThirteenPlanes.Cartan.ClassicalQuaternionicKilling
public import ThirteenPlanes.Cartan.ClassicalSymplecticComplex
public import ThirteenPlanes.Cartan.LieCompactConjugation

@[expose] public section

set_option backward.privateInPublic true

/-! Compact-form compatible Killing-orthogonal Cartan families in complex sp(6). -/

namespace ThirteenPlanes.Cartan

open LieAlgebra

noncomputable section

/-- A complex symplectic Cartan decomposition that is permuted by an arbitrary compact
conjugation descends, after a complex Lie automorphism, to compact sp(3). -/
theorem sp6C_cartanOD_descends_to_compactSp3 {ι : Type*} [DecidableEq ι]
    (H : ι → LieSubalgebra ℂ complexSp6) (hH : IsKillingCartanOD H)
    (σ : LieConjugation complexSp6) (hσ : σ.IsCompact) (π : Equiv.Perm ι)
    (hπ : ∀ i, σ '' (H i : Set complexSp6) = H (π i)) :
    ∃ T : ι → LieSubalgebra ℝ compactSp3, IsKillingCartanOD T := by
  let E := compactSp3ComplexEquiv.symm
  let H' (i : ι) := (H i).map E.toLieHom
  let σ' := σ.transport E
  let τ := (LieComplex.compactConjugation : LieConjugation (LieComplex compactSp3))
  have hH' : IsKillingCartanOD H' := killingCartanOD_map E H hH
  have hs' : σ'.IsCompact := LieConjugation.transport_compact E σ hσ
  have hπ' (i : ι) : σ' '' (H' i : Set (LieComplex compactSp3)) = H' (π i) :=
    conjugation_permutes_map E σ σ' (fun x => by simp [σ']) H π hπ i
  obtain ⟨e, he⟩ := τ.exists_intertwining_aut σ'
    (LieComplex.compactConjugation_isCompact compactSp3_compactKilling) hs'
    LieComplex.killing_conjugation_conjugation
  let H'' (i : ι) := (H' i).map e.toLieHom
  have hH'' : IsKillingCartanOD H'' := killingCartanOD_map e H' hH'
  have hπ'' (i : ι) : LieComplex.conjugation '' (H'' i : Set (LieComplex compactSp3)) = H'' (π i) :=
    conjugation_permutes_map e σ' τ he H' π hπ' i
  exact ⟨fun i => LieComplex.descend (H'' i),
    (compactCartanOD_descent compactSp3_compactKilling H'' hH'' π hπ'').2⟩

/-- The standard matrix conjugation, viewed as a conjugate-linear Lie involution. -/
def complexSp6CompactConjugation : LieConjugation complexSp6 where
  toFun := standardSp6Conjugation
  add := standardSp6Conjugation_add
  smul := standardSp6Conjugation_smul
  involutive := standardSp6Conjugation_involutive
  bracket := standardSp6Conjugation_lie

private theorem compact_conjugation_is_compact : complexSp6CompactConjugation.IsCompact := by
  have ht := LieConjugation.transport_compact compactSp3ComplexEquiv LieComplex.compactConjugation
    (LieComplex.compactConjugation_isCompact compactSp3_compactKilling)
  intro x hx
  have h := ht x hx
  change _ < 0 at h
  rw [LieConjugation.transport_apply, LieComplex.compactConjugation_apply,
    compactSp3ComplexEquiv_conjugation, LieEquiv.apply_symm_apply] at h
  exact h

/-- The two existence statements in the compact symplectic corollary are equivalent. -/
theorem compactSp3_cartanOD_iff_complex_compatible {ι : Type*} [DecidableEq ι] :
    (∃ T : ι → LieSubalgebra ℝ compactSp3, IsKillingCartanOD T) ↔
      ∃ (H : ι → LieSubalgebra ℂ complexSp6) (σ : LieConjugation complexSp6) (π : Equiv.Perm ι),
        IsKillingCartanOD H ∧ σ.IsCompact ∧
          ∀ i, σ '' (H i : Set complexSp6) = H (π i) := by
  constructor
  · rintro ⟨T,hT⟩
    let HE (i : ι) := LieComplex.extend (T i)
    let τ := (LieComplex.compactConjugation : LieConjugation (LieComplex compactSp3))
    let E := compactSp3ComplexEquiv
    have hHE : IsKillingCartanOD HE := compactCartanOD_complexification compactSp3_compactKilling T hT
    have hHE' (i : ι) : τ '' (HE i : Set (LieComplex compactSp3)) = HE ((Equiv.refl ι) i) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change y ∈ HE i at hy
        change LieComplex.conjugation y ∈ HE i
        simpa only [HE, LieComplex.mem_extend, LieComplex.realPart_conjugation,
          LieComplex.imagPart_conjugation, neg_mem_iff] using hy
      · intro hx
        change x ∈ HE i at hx
        refine ⟨τ x, ?_, τ.involutive x⟩
        change LieComplex.conjugation x ∈ HE i
        simpa only [HE, LieComplex.mem_extend, LieComplex.realPart_conjugation,
          LieComplex.imagPart_conjugation, neg_mem_iff] using hx
    exact ⟨fun i => (HE i).map E.toLieHom, complexSp6CompactConjugation, Equiv.refl ι,
      killingCartanOD_map E HE hHE, compact_conjugation_is_compact,
      conjugation_permutes_map E τ complexSp6CompactConjugation compactSp3ComplexEquiv_conjugation
        HE (Equiv.refl ι) hHE'⟩
  · rintro ⟨H,σ,π,hH,hσ,hπ⟩
    exact sp6C_cartanOD_descends_to_compactSp3 H hH σ hσ π hπ

end
end ThirteenPlanes.Cartan
