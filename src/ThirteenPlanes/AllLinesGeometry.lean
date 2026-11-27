/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.AllLines
public import ThirteenPlanes.FamilyVariance.Formula
public import ThirteenPlanes.PilotContractions
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

set_option backward.privateInPublic true

/-! The concrete four-plane identification on every projective charge line. -/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace ThirteenPlanes

private theorem opposite_representative_ne (p q : SignedPlaneIndex) :
    p.val ≠ oppositeCharge q.val := by
  intro h
  have hp := p.property
  rw [h, oppositeCharge_isRepresentative_iff] at hp
  exact hp q.property

private def representative (q : NonzeroCharge) : SignedPlaneIndex :=
  if h : isChargeRepresentative q.val then ⟨q, h⟩
  else ⟨oppositeCharge q, (oppositeCharge_isRepresentative_iff q).mpr h⟩

private theorem representative_pair (q : NonzeroCharge) :
    q = (representative q).val ∨ q = oppositeCharge (representative q).val := by
  by_cases h : isChargeRepresentative q.val
  · simp [representative, h]
  · simp [representative, h]

private theorem representative_of_pair (q : NonzeroCharge) (p : SignedPlaneIndex)
    (h : q = p.val ∨ q = oppositeCharge p.val) : representative q = p := by
  rcases h with rfl | rfl
  · simp [representative, p.property]
  · have hp : ¬ isChargeRepresentative (oppositeCharge p.val).val := by
      rw [oppositeCharge_isRepresentative_iff]
      exact not_not.mpr p.property
    apply Subtype.ext
    simp [representative, hp]

private theorem nonzeroEquiv_opposite (g : GradeLift) (q : NonzeroCharge) :
    g.nonzeroEquiv (oppositeCharge q) = oppositeCharge (g.nonzeroEquiv q) :=
  Subtype.ext (map_neg g.relabel q.val)

private def liftedPlaneIndex (g : GradeLift) (p : SignedPlaneIndex) : SignedPlaneIndex :=
  representative (g.nonzeroEquiv p.val)

private theorem liftedPlaneIndex_injective (g : GradeLift) : Function.Injective (liftedPlaneIndex g) := by
  intro p q h
  obtain hp | hp := representative_pair (g.nonzeroEquiv p.val) <;>
    obtain hq | hq := representative_pair (g.nonzeroEquiv q.val)
  · exact Subtype.ext (g.nonzeroEquiv.injective (hp.trans ((congrArg Subtype.val h).trans hq.symm)))
  · exfalso
    apply opposite_representative_ne p q
    apply g.nonzeroEquiv.injective
    rw [nonzeroEquiv_opposite, hq, oppositeCharge_opposite]
    exact hp.trans (congrArg Subtype.val h)
  · exfalso
    apply opposite_representative_ne p q
    apply g.nonzeroEquiv.injective
    rw [nonzeroEquiv_opposite, hq]
    exact hp.trans (congrArg (oppositeCharge ∘ Subtype.val) h)
  · exact Subtype.ext (g.nonzeroEquiv.injective
      (hp.trans ((congrArg (oppositeCharge ∘ Subtype.val) h).trans hq.symm)))

private theorem signedPlane_coordinate_eq_zero {p : SignedPlaneIndex} {x : SignedField}
    (hx : x ∈ signedPlane p) (q : NonzeroCharge) (hp : q ≠ p.val)
    (hm : q ≠ oppositeCharge p.val) : signedCoordinates x q = 0 := by
  obtain ⟨⟨r, s⟩, rfl⟩ := signedPlaneGradeEquiv.surjective q
  cases s
  · exact mem_signedPlane_iff.mp hx r fun e => hp (congrArg Subtype.val e)
  · rw [signedPlaneGradeEquiv_true, signedCoordinates_opposite]
    change star (signedPlaneCoordinates x r) = _
    rw [mem_signedPlane_iff.mp hx r (fun e => hm (congrArg (oppositeCharge ∘ Subtype.val) e)), star_zero]

private theorem liftedPlane_map (g : GradeLift) (p : SignedPlaneIndex) :
    (signedPlane p).map g.action.toLinearMap = signedPlane (liftedPlaneIndex g p) := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_signedPlane_iff.mpr
    intro q hqp
    let v := g.nonzeroEquiv.symm q.val
    have hv : g.nonzeroEquiv v = q.val := g.nonzeroEquiv.apply_symm_apply q.val
    have hp : v ≠ p.val := by
      intro he
      apply hqp
      exact (representative_of_pair _ q (Or.inl (he ▸ hv))).symm
    have hm : v ≠ oppositeCharge p.val := by
      intro he
      apply hqp
      rw [he, nonzeroEquiv_opposite] at hv
      have he' : g.nonzeroEquiv p.val = oppositeCharge q.val := by
        rw [← hv, oppositeCharge_opposite]
      exact (representative_of_pair _ q (Or.inr he')).symm
    change signedCoordinates (g.action x) q.val = 0
    rw [← hv, g.action_coordinates, signedPlane_coordinate_eq_zero hx _ hp hm, mul_zero]
  · rw [← ((signedPlane p).equivMapOfInjective g.action.toLinearMap g.action.injective).finrank_eq,
      signedPlane_finrank, signedPlane_finrank]

abbrev ChargeLinePoint (n : NonzeroCharge) := {p : SignedPlaneIndex // chargeDot n.val p.val.val = 0}

private theorem chargeLinePoint_card : ∀ n : NonzeroCharge, Fintype.card (ChargeLinePoint n) = 4 := by
  decide +kernel

private theorem chargeDot_neg_right (x y : Charge) : chargeDot x (-y) = -chargeDot x y := by
  simp [chargeDot, Finset.sum_neg_distrib]

private def liftedLinePoints (n : NonzeroCharge) (g : GradeLift)
    (hg : ∀ q, chargeDot n.val (g.relabel q) = 0 ↔ q 2 = 0) (k : Fin 4) : ChargeLinePoint n := by
  refine ⟨liftedPlaneIndex g (matrixLineGrade k), ?_⟩
  have h := (hg (matrixLineGrade k).val.val).mpr (matrixLineGrade_third k)
  obtain he | he := representative_pair (g.nonzeroEquiv (matrixLineGrade k).val)
  · have hh := congrArg (fun q : NonzeroCharge => chargeDot n.val q.val) he
    exact hh.symm.trans h
  · have hh := congrArg (chargeDot n.val ∘ Subtype.val) he
    change chargeDot n.val (g.relabel (matrixLineGrade k).val.val) =
      chargeDot n.val (-(liftedPlaneIndex g (matrixLineGrade k)).val.val) at hh
    rw [chargeDot_neg_right, h] at hh
    exact neg_eq_zero.mp hh.symm

private theorem liftedLinePoints_injective (n : NonzeroCharge) (g : GradeLift) (hg) :
    Function.Injective (liftedLinePoints n g hg) :=
  fun _ _ h => matrixLineGrade_injective (liftedPlaneIndex_injective g (congrArg Subtype.val h))

theorem liftedMatrixLine_cubic (g : GradeLift) (u : ℝ × ℝ) (x y z : TracelessHermitian3) :
    (coupling signedPair u).apply (liftedMatrixLine g x) (liftedMatrixLine g y) (liftedMatrixLine g z) =
      (coupling fourPlanePair u).apply x y z := by
  let j := liftedMatrixLine g
  let a := coupling signedPair u
  let b := coupling fourPlanePair u
  have hinner (v w : TracelessHermitian3) : ⟪j v, j w⟫ = ⟪v, w⟫ := by
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (j v),
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two v,
      ← j.map_add]
    simp only [j.norm_map]
  have h (v : TracelessHermitian3) : a.apply (j v) (j v) (j z) = b.apply v v z := by
    change ⟪a.squareMap (j v), j z⟫ = ⟪b.squareMap v, z⟫
    rw [liftedMatrixLine_square, hinner]
  have hh := h (x + y)
  simp only [map_add, SymmetricCubic.apply_add₁, SymmetricCubic.apply_add₂,
    a.apply_swap₁₂ (j y) (j x), b.apply_swap₁₂ y x, h x, h y] at hh
  change a.apply (j x) (j y) (j z) = b.apply x y z
  linarith

/-- Every projective line has the same cubic and four identified projector planes. -/
theorem matrixLine_over_any_normal_geometry (n : NonzeroCharge) :
    ∃ (j : TracelessHermitian3 →ₗᵢ[ℝ] SignedField) (e : Fin 4 ≃ ChargeLinePoint n),
      (∀ y : SignedField, y ∈ LinearMap.range j.toLinearMap ↔
        ∀ q : NonzeroCharge, chargeDot n.val q.val ≠ 0 → signedCoordinates y q = 0) ∧
      (∀ k, (matrixPlane k).map j.toLinearMap = signedPlane (e k).val) ∧
      (∀ (u : ℝ × ℝ) (x y z : TracelessHermitian3),
        (coupling signedPair u).apply (j x) (j y) (j z) = (coupling fourPlanePair u).apply x y z) := by
  obtain ⟨g, hg⟩ := lineLift_exists n
  have hcard : Fintype.card (Fin 4) = Fintype.card (ChargeLinePoint n) := by
    rw [Fintype.card_fin, chargeLinePoint_card]
  let e := Equiv.ofBijective (liftedLinePoints n g hg)
    ⟨liftedLinePoints_injective n g hg,
      (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mp
        (liftedLinePoints_injective n g hg)⟩
  refine ⟨liftedMatrixLine g, e, liftedMatrixLine_range n g hg, ?_, liftedMatrixLine_cubic g⟩
  intro k
  change (matrixPlane k).map (g.action.toLinearMap.comp matrixLineEmbed.toLinearMap) =
    signedPlane (liftedPlaneIndex g (matrixLineGrade k))
  rw [Submodule.map_comp, matrixLineEmbed_matrixPlane, liftedPlane_map]

/-- The restricted diagonal and mixing cubics on each projective charge line have Gram entries
`8/3`, `4` and `0`. The isometry realizes the restriction on the kinetic matrix carrier. -/
theorem matrixLine_over_any_normal_gram (n : NonzeroCharge) :
    ∃ j : TracelessHermitian3 →ₗᵢ[ℝ] SignedField,
      (∀ y : SignedField, y ∈ LinearMap.range j.toLinearMap ↔
        ∀ q : NonzeroCharge, chargeDot n.val q.val ≠ 0 → signedCoordinates y q = 0) ∧
      let d : SymmetricCubic TracelessHermitian3 := signedPair.diagonalCubic.pullback j.toLinearMap
      let m : SymmetricCubic TracelessHermitian3 := signedPair.mixingCubic.pullback j.toLinearMap
      d.tensorPairing d = 8 / 3 ∧ m.tensorPairing m = 4 ∧ d.tensorPairing m = 0 := by
  obtain ⟨j, _, hrange, _, hcubic⟩ := matrixLine_over_any_normal_geometry n
  refine ⟨j, hrange, ?_⟩
  have hd : signedPair.diagonalCubic.pullback (W := TracelessHermitian3) j.toLinearMap =
      fourPlanePair.diagonalCubic := by
    apply SymmetricCubic.ext
    intro x y z
    simpa [coupling_apply] using hcubic (1, 0) x y z
  have hm : signedPair.mixingCubic.pullback (W := TracelessHermitian3) j.toLinearMap =
      fourPlanePair.mixingCubic := by
    apply SymmetricCubic.ext
    intro x y z
    simpa [coupling_apply] using hcubic (0, 1) x y z
  dsimp only
  rw [hd, hm]
  have hgram := gram_of_contractionLaws fourPlane_contractionLaws
  norm_num [fourPlane_dimension] at hgram
  exact hgram

end ThirteenPlanes
