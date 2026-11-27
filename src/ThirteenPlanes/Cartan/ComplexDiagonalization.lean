module

public import ThirteenPlanes.Cartan.ComplexUnitary
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

@[expose] public section

set_option backward.privateInPublic true

/-! A common special-unitary eigenbasis for a family in the compact complex matrix algebra. -/

namespace ThirteenPlanes.Cartan

open RoundCubics Module.End WithLp
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

private abbrev C3 := EuclideanSpace ℂ (Fin 3)

private theorem imaginary_times_hermitian (A : complexSkewTracelessMatrices) :
    (Complex.I • (A.val : ComplexMatrix3)).IsHermitian := by
  change (Complex.I • (A.val : ComplexMatrix3))ᴴ = _
  rw [Matrix.conjTranspose_smul, A.property.1, Complex.star_def, Complex.conj_I,
    neg_smul, smul_neg, neg_neg]

set_option maxHeartbeats 450000 in
private theorem complex_skew_jointEigenbasis {ι : Type*} (A : ι → complexSkewTracelessMatrices)
    (hc : Pairwise fun i j => Commute (A i).val (A j).val) :
    ∃ (b : OrthonormalBasis (Fin 3) ℂ C3) (c : ι → Fin 3 → ℂ),
      ∀ i j, (A i).val *ᵥ ⇑(b j) = c i j • ⇑(b j) := by
  classical
  let T (i : ι) : Module.End ℂ C3 := (Complex.I • (A i).val).toEuclideanLin
  have hT (i) : (T i).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (imaginary_times_hermitian (A i))
  have hTc : Pairwise fun i j => Commute (T i) (T j) := by
    intro i j hij
    apply LinearMap.ext
    intro x
    apply WithLp.ofLp_injective
    simp only [T, mul_apply_eq_comp, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec, Matrix.smul_mul, Matrix.mul_smul, (hc hij).eq]
  let W (μ : ι → ℂ) : Submodule ℂ C3 := ⨅ i, eigenspace (T i) (μ i)
  let hO := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  let hD := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hTc
  let bW (μ : ι → ℂ) : OrthonormalBasis (Fin (Module.finrank ℂ (W μ))) ℂ (W μ) :=
    stdOrthonormalBasis ℂ (W μ)
  let raw : Module.Basis (Σ μ : ι → ℂ, Fin (Module.finrank ℂ (W μ))) ℂ C3 :=
    hD.collectedBasis (fun μ => (bW μ).toBasis)
  let : Finite (Σ μ : ι → ℂ, Fin (Module.finrank ℂ (W μ))) := Module.Finite.finite_basis raw
  let : Fintype (Σ μ : ι → ℂ, Fin (Module.finrank ℂ (W μ))) := Fintype.ofFinite _
  have hB : Orthonormal ℂ raw :=
    DirectSum.IsInternal.collectedBasis_orthonormal hO hD
      (v_family := fun μ => (bW μ).toBasis)
      (fun μ => by simpa only [OrthonormalBasis.coe_toBasis] using (bW μ).orthonormal)
  let B := raw.toOrthonormalBasis hB
  have hcard : Fintype.card (Σ μ : ι → ℂ, Fin (Module.finrank ℂ (W μ))) = 3 :=
    (Module.finrank_eq_card_basis raw).symm.trans (by simp [C3])
  let index := (Fintype.equivFinOfCardEq hcard).symm
  let b : OrthonormalBasis (Fin 3) ℂ C3 := B.reindex index.symm
  have heigen (i : ι) (j : Fin 3) : T i (b j) = (index j).1 i • b j := by
    have h : raw (index j) ∈ W (index j).1 :=
      hD.collectedBasis_mem (fun μ => (bW μ).toBasis) (index j)
    have hb : b j = raw (index j) := by
      rw [show b = B.reindex index.symm from rfl, OrthonormalBasis.reindex_apply,
        Equiv.symm_symm]
      simp [B]
    rw [hb]
    exact mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp h i)
  refine ⟨b, fun i j => (-Complex.I) * (index j).1 i, ?_⟩
  intro i j
  have h := congrArg (fun x : C3 => WithLp.ofLp x) (heigen i j)
  change ofLp ((Complex.I • (A i).val).toEuclideanLin (b j)) =
    ofLp ((index j).1 i • b j) at h
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.smul_mulVec, WithLp.ofLp_smul] at h
  have h' := congrArg (fun w : Fin 3 → ℂ => (-Complex.I) • w) h
  simpa only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] using h'

private theorem unitary_diagonalization_from_eigenbasis {ι : Type*}
    (A : ι → complexSkewTracelessMatrices) (b : OrthonormalBasis (Fin 3) ℂ C3)
    (c : ι → Fin 3 → ℂ) (hef : ∀ i j, (A i).val *ᵥ ⇑(b j) = c i j • ⇑(b j)) :
    ∃ U : ComplexUnitary3, ∀ i,
      complexMatrixAd (star U) (A i).val = Matrix.diagonal (c i) := by
  let std := EuclideanSpace.basisFun (Fin 3) ℂ
  let U : ComplexUnitary3 :=
    ⟨std.toBasis.toMatrix b.toBasis, std.toMatrix_orthonormalBasis_mem_unitary b⟩
  have hU (j : Fin 3) : U.val *ᵥ Pi.single j 1 = ⇑(b j) := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hUs (j : Fin 3) : U.valᴴ *ᵥ ⇑(b j) = Pi.single j 1 := by
    rw [← hU, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mulVec]
  refine ⟨U, ?_⟩
  intro i
  apply Matrix.ext
  intro k j
  have had : complexMatrixAd (star U) (A i).val = U.valᴴ * (A i).val * U.val := by
    simp [complexMatrixAd_apply, Matrix.star_eq_conjTranspose]
  have h : (complexMatrixAd (star U) (A i).val) *ᵥ Pi.single j 1 =
      Matrix.diagonal (c i) *ᵥ Pi.single j 1 := by
    rw [had, mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU, hef,
      Matrix.mulVec_smul, hUs, Matrix.diagonal_mulVec_single]
    funext l
    by_cases hl : l = j <;> simp [Pi.single_apply, hl, eq_comm]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun h k

/-- Every commuting family of actual traceless skew-Hermitian matrices has one
special-unitary conjugator into the traceless imaginary diagonal. -/
theorem complexSkew_simultaneousDiagonalization {ι : Type*} (A : ι → complexSkewTracelessMatrices)
    (hc : Pairwise fun i j => Commute (A i).val (A j).val) :
    ∃ U : ComplexSpecialUnitary3, ∀ i, ∃ a : Fin 3 → ℝ, (∑ k, a k = 0) ∧
      complexMatrixAd (⟨U.val, U.property.1⟩ : ComplexUnitary3) (A i).val =
        Matrix.diagonal (fun k => a k • Complex.I) := by
  obtain ⟨b, c, hef⟩ := complex_skew_jointEigenbasis A hc
  obtain ⟨U, hdiag⟩ := unitary_diagonalization_from_eigenbasis A b c hef
  obtain ⟨U', hU'⟩ := complexUnitary_exists_SU3_sameMatrixAd (star U)
  refine ⟨U', fun i => ?_⟩
  rw [hU']
  have hDskew : (Matrix.diagonal (c i))ᴴ = -Matrix.diagonal (c i) := by
    rw [← hdiag, ← Matrix.star_eq_conjTranspose, ← map_star]
    change complexMatrixAd (star U) ((A i).valᴴ) = _
    rw [(A i).property.1, map_neg]
  have hDtrace : Matrix.trace (Matrix.diagonal (c i)) = 0 := by
    rw [← hdiag, complexMatrixAd_preserves_trace]
    exact (A i).property.2
  refine ⟨fun j => (c i j).im, ?_, ?_⟩
  · have he := congrArg Complex.im hDtrace
    simpa [Matrix.trace_diagonal, Fin.sum_univ_three] using he
  · rw [hdiag]
    congr 1
    funext j
    have he := congrArg (fun M : ComplexMatrix3 => (M j j).re) hDskew
    have hre : (c i j).re = 0 := by
      simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at he
      linarith
    apply Complex.ext
    · simpa [Complex.real_smul] using hre
    · simp [Complex.real_smul]

end

end ThirteenPlanes.Cartan
