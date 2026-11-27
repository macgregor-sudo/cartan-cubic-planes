module

public import ThirteenPlanes.Peirce.SlotClosedPlaneIdentification
public import ThirteenPlanes.MixedGram

@[expose] public section

/-! The four-plane branch of the pair-octet corollary at arbitrary round strength. -/

open scoped InnerProductSpace

namespace ThirteenPlanes.JordanFrames

noncomputable section

open Peirce RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] {h : SymmetricCubic V} {c : ℝ} {planes : PlaneDecomposition V ι}

/-- In a system of four closed planes the pair, together with its mixed-product space,
exhausts the eight-dimensional ambient space. -/
theorem pairOctet_fourPlanes_eq_top (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (hm : Fintype.card ι = 4) {i j : ι} (hij : i ≠ j) :
    (planes.plane i ⊔ planes.plane j) ⊔ mixedProductSpace h (planes.plane i) (planes.plane j) = ⊤ := by
  let M := mixedProductSpace h (planes.plane i) (planes.plane j)
  let A := planes.plane i ⊔ planes.plane j
  have ho := planes.pairwise_orthogonal hij
  have hM : Module.finrank ℝ M = 4 :=
    mixedProductSpace_finrank round ho (closed i) (closed j) (planes.dimension i) (planes.dimension j)
  have hA := Submodule.finrank_sup_add_finrank_inf_eq (planes.plane i) (planes.plane j)
  rw [ho.disjoint.eq_bot, finrank_bot, add_zero, planes.dimension, planes.dimension] at hA
  have hMA : M.IsOrtho A := Submodule.isOrtho_iff_le.mpr
    (mixedProductSpace_le_orthogonal round ho (closed i) (closed j))
  have hAM := Submodule.finrank_sup_add_finrank_inf_eq A M
  rw [hMA.symm.disjoint.eq_bot, finrank_bot, add_zero, hA, hM] at hAM
  apply Submodule.eq_top_of_finrank_eq
  rw [hAM, finrank_eq_twice_card planes, hm]

/-- The four-plane branch of Corollary 3-octet, at any positive strength. -/
theorem pairOctet_fourPlanes (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (hm : Fintype.card ι = 4) {i j : ι} (hij : i ≠ j) :
    let S := (planes.plane i ⊔ planes.plane j) ⊔ mixedProductSpace h (planes.plane i) (planes.plane j)
    IsClosedPiece h S ∧ ∃ I : S ≃ₗᵢ[ℝ] TracelessHermitian3,
      h.pullback S.subtype = Real.sqrt c • complexCartanCubic.pullback I.toLinearMap := by
  dsimp only
  let S := (planes.plane i ⊔ planes.plane j) ⊔ mixedProductSpace h (planes.plane i) (planes.plane j)
  change IsClosedPiece h S ∧ ∃ I : S ≃ₗᵢ[ℝ] TracelessHermitian3, _
  have hS : S = ⊤ := pairOctet_fourPlanes_eq_top round closed hm hij
  let t := Real.sqrt c
  have ht : 0 < t := Real.sqrt_pos.mpr round.positive
  let g := t⁻¹ • h
  have hg : IsRound g 1 := by
    refine ⟨by norm_num, fun x => ?_⟩
    change ‖(t⁻¹ • h).squareMap x‖ ^ 2 = _
    have hscale : (t⁻¹) ^ 2 * c = 1 := by
      rw [inv_pow, show t ^ 2 = c from Real.sq_sqrt round.positive.le,
        inv_mul_cancel₀ round.positive.ne']
    rw [SymmetricCubic.squareMap_smul, norm_smul, mul_pow, Real.norm_of_nonneg (inv_nonneg.mpr ht.le),
      round.square_norm, ← mul_assoc, hscale, one_mul]
  have hgc : IsClosedPlaneSystem g planes := by
    intro k x y hx hy
    change (t⁻¹ • h).L x y ∈ planes.plane k
    simpa only [map_smul, LinearMap.smul_apply] using (planes.plane k).smul_mem t⁻¹ (closed k hx hy)
  obtain ⟨I, hI, _⟩ := closedPlaneSystem_complex hg hgc hm i
  let J : S ≃ₗᵢ[ℝ] V :=
    ⟨LinearEquiv.ofBijective S.subtype ⟨S.subtype_injective, fun x => ⟨⟨x, hS ▸ trivial⟩, rfl⟩⟩,
      fun _ => rfl⟩
  refine ⟨?_, J.trans I, ?_⟩
  · intro x y hx hy
    rw [hS]
    trivial
  · have hh : h = t • g := by
      change h = t • (t⁻¹ • h)
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    apply SymmetricCubic.ext
    intro x y z
    rw [SymmetricCubic.pullback_apply, SymmetricCubic.apply_smul, SymmetricCubic.pullback_apply]
    change h.apply (J x) (J y) (J z) = t * complexCartanCubic.apply (I (J x)) (I (J y)) (I (J z))
    calc
      _ = (t • g).apply (J x) (J y) (J z) :=
        congrArg (fun k : SymmetricCubic V => k.apply (J x) (J y) (J z)) hh
      _ = _ := by
        rw [SymmetricCubic.apply_smul, hI, SymmetricCubic.pullback_apply]
        rfl

end

end ThirteenPlanes.JordanFrames
