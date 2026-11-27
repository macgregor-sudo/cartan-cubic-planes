module

public import ThirteenPlanes.Cartan.GradeRealAlbert
public import ThirteenPlanes.Cartan.DerivationGradingAlbertMetric
public import ThirteenPlanes.Cartan.AlbertDerivationComplexCoordinates

@[expose] public section

set_option backward.privateInPublic true

/-! The native graded Cartan decomposition and both of its orthogonality relations. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading LieAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)

private theorem gradePair_trace_zero {g h : Charge} (hne : g ≠ h) (hopp : g ≠ -h)
    {X Y : Module.End ℂ JC}
    (hx : X ∈ (albertGradingBasis hρ).gradePair g)
    (hy : Y ∈ (albertGradingBasis hρ).gradePair h) :
    LinearMap.trace ℂ JC (X * Y) = 0 := by
  let M := albertGradingBasis hρ
  let : Module.Finite ℂ JC := Module.Finite.of_basis M.basis
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  have hz (r s : Charge) (h : r ≠ -s) : r + s ≠ 0 := fun e => h (eq_neg_of_add_eq_zero_left e)
  have degA := (M.mem_derivationGrade.mp ha).2
  have degB := (M.mem_derivationGrade.mp hb).2
  have degC := (M.mem_derivationGrade.mp hc).2
  have degD := (M.mem_derivationGrade.mp hd).2
  have h₁ := M.trace_mul_eq_zero_of_nonopposite (hz g h hopp) degA degC
  have h₂ := M.trace_mul_eq_zero_of_nonopposite (hz g (-h) (by simpa using hne)) degA degD
  have h₃ := M.trace_mul_eq_zero_of_nonopposite
    (hz (-g) h (fun e => hne (neg_injective e))) degB degC
  have h₄ := M.trace_mul_eq_zero_of_nonopposite
    (hz (-g) (-h) (fun e => hopp (neg_injective e))) degB degD
  simp only [add_mul, mul_add, map_add, h₁, h₂, h₃, h₄, add_zero]

private theorem albertGradingRep_ofReal_mapC (X : NativeAlbertDerivations) :
    albertGradingRep (LieComplex.ofReal X) = JC.mapC X.val := by
  change (albertDerivationComplexEquiv (LieComplex.ofReal X)).val = _
  rw [albertDerivationComplexEquiv_apply_ofReal, extendAlbertDerivation_val]

/-- The actual native operator trace is orthogonal across distinct real opposite-grade pairs. -/
theorem albertGradingRealCartans_trace_orthogonal :
    Pairwise fun p q : SignedPlaneIndex =>
      ∀ X ∈ albertGradingRealCartan hρ p, ∀ Y ∈ albertGradingRealCartan hρ q,
      nativeAlbertTracePairing X Y = 0 := by
  intro p q hpq X hx Y hy
  have hne := representatives_not_eq_or_neg hpq
  have hx' := (albertComplexGradePair_mem hρ p (LieComplex.ofReal X)).mp hx
  have hy' := (albertComplexGradePair_mem hρ q (LieComplex.ofReal Y)).mp hy
  have ht := gradePair_trace_zero hρ hne.1 hne.2 hx' hy'
  rw [albertGradingRep_ofReal_mapC, albertGradingRep_ofReal_mapC] at ht
  have hm : JC.mapC (0 : Module.End ℝ Glennie.Albert) = 0 := by
    apply LinearMap.ext
    intro x
    apply JC.ext <;> rfl
  have he := jcTraceForm_realImag X.val 0 Y.val 0
  simp only [hm, smul_zero, add_zero, mul_zero, zero_mul, map_zero, Complex.ofReal_zero, sub_zero, ht, neg_zero] at he
  rw [nativeAlbertTracePairing_apply]
  exact Complex.ofReal_eq_zero.mp he.symm

theorem albertGradingRealCartan_isCartan (p : SignedPlaneIndex) :
    (albertGradingRealCartan hρ p).IsCartanSubalgebra :=
  cartan_of_definiteInvariant nativeAlbertTracePairing nativeAlbertTracePairing_definite
    nativeAlbertTracePairing_invariant _ (albertGradingRealCartan_selfCentralizing hρ p)

/-- Proposition 7-f4-graded. For any native ternary action with the prescribed grading,
the literal opposite-character intersections form a complete compact Cartan decomposition
and their fixed spaces are the marked graded planes. -/
/- For the complex F₄ Jordan grading and the opposite-grade Cartan decomposition, see
Alberto Elduque (arXiv:0810.2737, §1 and Theorem 3.5) and Kostrikin–Tiep (1994,
Theorem 3.1.2, pp. 85–86). The proof here checks orthogonality by the invariant trace
pairing and proves commutativity in the two-dimensional grades. -/
theorem ternaryGrading_derivationCartanOD :
    IsKillingCartanOD (albertGradingRealCartan hρ) ∧
      (∀ p, Module.finrank ℝ (albertGradingRealCartan hρ p) = 4) ∧
      (Pairwise fun p q : SignedPlaneIndex =>
        ∀ X ∈ albertGradingRealCartan hρ p, ∀ Y ∈ albertGradingRealCartan hρ q,
        nativeAlbertTracePairing X Y = 0) ∧
      ∀ p, albertRealFixed (albertGradingRealCartan hρ p) = pointPlane ρ p :=
  ⟨⟨albertGradingRealCartan_isCartan hρ, albertGradingRealCartans_killing_orthogonal hρ,
      albertGradingRealCartans_isInternal hρ⟩, albertGradingRealCartan_finrank hρ,
    albertGradingRealCartans_trace_orthogonal hρ, albertGradingRealCartan_fixedPlane hρ⟩

/-- A native ternary grading also witnesses negative definiteness of the actual compact Killing form. -/
theorem nativeAlbert_compactKilling_of_grading (hgrade : IsTernaryGrading ρ) :
    CompactKilling NativeAlbertDerivations := by
  apply nativeAlbert_compactKilling_of_centerFree
  intro X hX
  have hall (p : SignedPlaneIndex) : X ∈ (albertGradingRealCartan hgrade p).toSubmodule :=
    (albertGradingRealCartan_selfCentralizing hgrade p X).mp (fun Y _ => hX Y)
  let : Nontrivial SignedPlaneIndex := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [signedPlaneIndex_card]
    decide)
  obtain ⟨p, q, hpq⟩ := exists_pair_ne SignedPlaneIndex
  have hd := (albertGradingRealCartans_isInternal hgrade).submodule_iSupIndep.pairwiseDisjoint hpq
  exact (Submodule.disjoint_def.mp hd) X (hall p) (hall q)

end

end ThirteenPlanes.Cartan
