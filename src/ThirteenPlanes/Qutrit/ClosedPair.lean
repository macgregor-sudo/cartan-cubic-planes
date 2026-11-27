module

public import ThirteenPlanes.Qutrit.Octet
public import ThirteenPlanes.Peirce.UnitIdempotent
public import ThirteenPlanes.FourPlanesDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! The pair octet is intrinsic to the two closed planes. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

noncomputable section

open Peirce RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : SymmetricCubic V} {U Y : Submodule ℝ V}

private theorem markedPair_in_closedPlane (round : IsRound h 1) (closed : IsClosedPiece h U)
    (dim : Module.finrank ℝ U = 2) :
    ∃ (a : V) (b : minusSpace h a),
      a ∈ U ∧ (b : V) ∈ U ∧ IsUnitIdempotent h a ∧ ‖b‖ = 1 := by
  let k := h.pullback U.subtype
  have kr := closedSubspace_restriction_isRound round closed
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨a, ha⟩ := exists_unitIdempotent k kr
  have ha₀ : a ≠ 0 := by
    intro hz
    have := ha.norm_eq_one
    simp [hz] at this
  let : Fact (Module.finrank ℝ U = 1 + 1) := ⟨dim⟩
  let v := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1 ha₀
  let b : U := v 0
  have hb : ‖b‖ = 1 := v.orthonormal.norm_eq_one 0
  have ho : ⟪a, b⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self a) (v 0).property
  let e : Fin 2 → U := ![a, b]
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · change ⟪a, a⟫ = 1
      rw [real_inner_self_eq_norm_sq, ha.norm_eq_one, one_pow]
    · exact ho
    · exact (real_inner_comm _ _).trans ho
    · change ⟪b, b⟫ = 1
      rw [real_inner_self_eq_norm_sq, hb, one_pow]
  have card : Fintype.card (Fin 2) = Module.finrank ℝ U := by simpa using dim.symm
  let B := basisOfOrthonormalOfCardEqFinrank he card
  have hB : ⇑B = e := coe_basisOfOrthonormalOfCardEqFinrank he card
  let E := B.toOrthonormalBasis (by rw [hB]; exact he)
  have hE : ⇑E = e := (Module.Basis.coe_toOrthonormalBasis B _).trans hB
  have ht := traceFree_of_round_finrank_two kr dim a
  rw [SymmetricCubic.trace_eq_sum_inner E, hE, Fin.sum_univ_two] at ht
  change ⟪a, k.L a a⟫ + ⟪b, k.L a b⟫ = 0 at ht
  rw [ha.square_eq_self, real_inner_self_eq_norm_sq, ha.norm_eq_one, one_pow] at ht
  have hab : k.L a b = -b := by
    have hr := E.sum_repr' (k.L a b)
    rw [hE, Fin.sum_univ_two] at hr
    change ⟪a, k.L a b⟫ • a + ⟪b, k.L a b⟫ • b = k.L a b at hr
    have hfirst : ⟪a, k.L a b⟫ = 0 := by
      rw [← k.L_isSymmetric a a b, ha.square_eq_self, ho]
    rw [hfirst, show ⟪b, k.L a b⟫ = -1 by linarith, zero_smul, zero_add, neg_one_smul] at hr
    exact hr.symm
  have hA : IsUnitIdempotent h (a : V) := ⟨ha.norm_eq_one, by
    rw [← closedSubspace_restriction_product closed, ha.square_eq_self]⟩
  have hB' : (b : V) ∈ minusSpace h (a : V) := Module.End.mem_eigenspace_iff.mpr (by
    rw [← closedSubspace_restriction_product closed, hab]
    simp)
  exact ⟨a, ⟨b, hB'⟩, a.property, b.property, hA, hb⟩

/-- A pair of closed orthogonal planes produces a closed octet with the complex trace product. -/
theorem closedPair_complexOctet (round : IsRound h (1 / 6)) (orth : U.IsOrtho Y)
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h Y)
    (dim : Module.finrank ℝ U = 2) (dim' : Module.finrank ℝ Y = 2) :
    let S := (U ⊔ Y) ⊔ mixedProductSpace h U Y
    IsClosedPiece h S ∧ ∃ I : S ≃ₗᵢ[ℝ] TracelessHermitian3,
      h.pullback S.subtype = matrixEqualCubic.pullback I.toLinearMap := by
  dsimp only
  let s := Real.sqrt 6
  have hs : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  let g := s • h
  have gRound : IsRound g 1 := by
    refine ⟨by norm_num, fun x => ?_⟩
    change ‖(s • h).squareMap x‖ ^ 2 = _
    rw [SymmetricCubic.squareMap_smul, norm_smul, Real.norm_of_nonneg hs.le, mul_pow, round.square_norm,
      show s ^ 2 = 6 from Real.sq_sqrt (by norm_num)]
    ring
  have hc {W : Submodule ℝ V} (H : IsClosedPiece h W) : IsClosedPiece g W := by
    intro x y hx hy
    change s • h.L x y ∈ W
    exact W.smul_mem _ (H hx hy)
  obtain ⟨a, b, haU, hbU, ha, hb⟩ := markedPair_in_closedPlane gRound (hc closed) dim
  have hex := pairOctet_isometry_unit gRound orth (hc closed) (hc closed') dim dim' a b haU hbU ha hb
  dsimp only at hex
  rw [show mixedProductSpace g U Y = _ from product_space_smul s hs.ne'] at hex
  obtain ⟨I, hI⟩ := hex
  refine ⟨pairOctet_closed round orth closed closed' dim dim', I, ?_⟩
  apply SymmetricCubic.ext
  intro x y z
  have he := congrArg (fun q => SymmetricCubic.apply q x y z) hI
  rw [SymmetricCubic.pullback_apply, SymmetricCubic.pullback_apply, complexCartanCubic] at he
  change (s • h).apply (x : V) (y : V) (z : V) =
    (s • matrixEqualCubic).apply (I x) (I y) (I z) at he
  rw [SymmetricCubic.apply_smul, SymmetricCubic.apply_smul] at he
  rw [SymmetricCubic.pullback_apply, SymmetricCubic.pullback_apply]
  exact mul_left_cancel₀ hs.ne' he

end

end ThirteenPlanes.JordanFrames
