module

public import ThirteenPlanes.RoundContractions
public import ThirteenPlanes.ClosedPieces

@[expose] public section

/-! The square sum of the orthogonal complement of closed planes of a harmonic round cubic.

For an orthonormal basis `(e a)` the vector `∑ a, h.L (e a) (e a)` vanishes when the cubic is
trace free (it is the Riesz vector of `x ↦ tr (h.L x)`). A closed plane of a round cubic carries a
trace-free restriction (`traceFree_of_round_finrank_two`), so each closed plane
contributes zero. Hence any orthonormal basis of the complement of a family of pairwise
orthogonal closed planes also has `h.L x x + h.L y y = 0` when that complement is a plane. -/

namespace ThirteenPlanes.AlbertGrading.CompletionO

open scoped BigOperators RealInnerProductSpace
open ThirteenPlanes ThirteenPlanes.RoundCubics Module

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- For a trace-free cubic, the diagonal square sum of an orthonormal basis vanishes. -/
theorem sum_L_diag_eq_zero {g : SymmetricCubic W} (tf : g.TraceFree) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ W) : ∑ a, g.L (e a) (e a) = 0 := by
  apply ext_inner_left ℝ
  intro x
  rw [inner_sum, inner_zero_right, ← tf x, ← PlaneContractions.sum_apply_diag e]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc
    ⟪x, g.L (e a) (e a)⟫ = g.apply (e a) (e a) x := real_inner_comm _ _
    _ = g.apply x (e a) (e a) :=
      ((g.apply_swap₁₂ x (e a) (e a)).trans (g.apply_swap₂₃ (e a) x (e a))).symm

/-- Each closed plane of a round cubic has zero diagonal square sum in any orthonormal basis. -/
theorem closedPlane_sum_L_diag {h : SymmetricCubic W} {c : ℝ} (round : IsRound h c)
    {U : Submodule ℝ W} (closed : IsClosedPiece h U) (hdim : finrank ℝ U = 2)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ U) :
    ∑ a, h.L (b a : W) (b a : W) = 0 := by
  have tf := traceFree_of_round_finrank_two (closedSubspace_restriction_isRound round closed) hdim
  have hs := congrArg (fun z : U => (z : W)) (sum_L_diag_eq_zero tf b)
  simpa only [Submodule.coe_sum, closedSubspace_restriction_product closed,
    Submodule.coe_zero] using hs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complement block followed by the given planes. -/
def blockSpace (P : ι → Submodule ℝ W) : Option ι → Submodule ℝ W
  | none => (⨆ i, P i)ᗮ
  | some i => P i

theorem blockSpace_orthogonal (P : ι → Submodule ℝ W)
    (orth : Pairwise fun i j => (P i).IsOrtho (P j)) :
    Pairwise fun k l => (blockSpace P k).IsOrtho (blockSpace P l) := by
  have hc (i : ι) : ((⨆ i, P i)ᗮ).IsOrtho (P i) :=
    Submodule.isOrtho_iff_le.mpr (Submodule.orthogonal_le (le_iSup P i))
  rintro (_ | i) (_ | j) hkl
  · exact (hkl rfl).elim
  · exact hc j
  · exact (hc i).symm
  · exact orth fun hij => hkl (congrArg some hij)

theorem blockSpace_iSup (P : ι → Submodule ℝ W) : ⨆ k, blockSpace P k = ⊤ := by
  rw [iSup_option]
  change (⨆ i, P i)ᗮ ⊔ ⨆ i, P i = ⊤
  rw [sup_comm]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

theorem blockSpace_family (P : ι → Submodule ℝ W)
    (orth : Pairwise fun i j => (P i).IsOrtho (P j)) :
    OrthogonalFamily ℝ (fun k => blockSpace P k) fun k => (blockSpace P k).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise (blockSpace_orthogonal P orth)

theorem blockSpace_internal (P : ι → Submodule ℝ W)
    (orth : Pairwise fun i j => (P i).IsOrtho (P j)) :
    DirectSum.IsInternal fun k => blockSpace P k := by
  exact (blockSpace_family P orth).isInternal_iff.mpr (by simp [blockSpace_iSup])

/-- The complement of pairwise orthogonal planes has the complementary dimension. -/
theorem finrank_complement_add (P : ι → Submodule ℝ W)
    (orth : Pairwise fun i j => (P i).IsOrtho (P j)) (hdim : ∀ i, finrank ℝ (P i) = 2) :
    finrank ℝ (⨆ i, P i)ᗮ + 2 * Fintype.card ι = finrank ℝ W := by
  let e := (blockSpace_internal P orth).collectedOrthonormalBasis (blockSpace_family P orth)
    fun k => stdOrthonormalBasis ℝ (blockSpace P k)
  rw [Module.finrank_eq_card_basis e.toBasis, Fintype.card_sigma, Fintype.sum_option]
  simp only [Fintype.card_fin]
  change finrank ℝ (⨆ i, P i)ᗮ + 2 * Fintype.card ι =
    finrank ℝ (⨆ i, P i)ᗮ + ∑ i, finrank ℝ (P i)
  simp only [hdim, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

/-- Orthonormal bases of the blocks, all indexed by `Fin 2`. -/
def blockBasis (P : ι → Submodule ℝ W) (hdim : ∀ i, finrank ℝ (P i) = 2)
    (b : OrthonormalBasis (Fin 2) ℝ (⨆ i, P i)ᗮ) :
    ∀ k, OrthonormalBasis (Fin 2) ℝ (blockSpace P k)
  | none => b
  | some i => (stdOrthonormalBasis ℝ (P i)).reindex (finCongr (hdim i))

/-- An orthonormal basis of a complementary plane of pairwise orthogonal closed planes of a harmonic
round cubic has square sum zero. -/
theorem complement_square_sum {h : SymmetricCubic W} {c : ℝ} (round : IsRound h c)
    (tf : h.TraceFree) (P : ι → Submodule ℝ W) (hdim : ∀ i, finrank ℝ (P i) = 2)
    (closed : ∀ i, IsClosedPiece h (P i)) (orth : Pairwise fun i j => (P i).IsOrtho (P j))
    (b : OrthonormalBasis (Fin 2) ℝ (⨆ i, P i)ᗮ) :
    h.L (b 0 : W) (b 0 : W) + h.L (b 1 : W) (b 1 : W) = 0 := by
  let e := (blockSpace_internal P orth).collectedOrthonormalBasis (blockSpace_family P orth)
    (blockBasis P hdim b)
  have he (k : Option ι) (j : Fin 2) : e ⟨k, j⟩ = (blockBasis P hdim b k j : W) := by
    simp [e, DirectSum.IsInternal.collectedOrthonormalBasis]
  have hs := sum_L_diag_eq_zero tf e
  rw [Fintype.sum_sigma, Fintype.sum_option] at hs
  simp only [he] at hs
  have hp (i : ι) : ∑ j : Fin 2, h.L (blockBasis P hdim b (some i) j : W)
      (blockBasis P hdim b (some i) j : W) = 0 :=
    closedPlane_sum_L_diag round (closed i) (hdim i) _
  rw [Finset.sum_congr rfl (fun i _ => hp i), Finset.sum_const_zero, add_zero,
    Fin.sum_univ_two] at hs
  exact hs

end

end ThirteenPlanes.AlbertGrading.CompletionO
