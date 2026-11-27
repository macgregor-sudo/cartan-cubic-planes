module

public import ThirteenPlanes.Shares.PGThree
public import ThirteenPlanes.Shares.AffineQuartetGraphs

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin 13)}

variable (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
  (cover : ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)
  {lInf : PlaneQuartetLine h system} (A : QuartetAffineAxes (h := h) (system := system) lInf)

private abbrev SlopePoint :=
  {p : Fin 13 // p ∈ lInf ∧ p ≠ A.rowInf ∧ p ≠ A.colInf}

omit [FiniteDimensional ℝ V] in
private theorem slope_point_card : Nat.card (SlopePoint A) = 2 := by
  let S := (lInf.val.erase A.rowInf).erase A.colInf
  have hs (p : Fin 13) : p ∈ S ↔ p ∈ lInf ∧ p ≠ A.rowInf ∧ p ≠ A.colInf := by
    change p ∈ S ↔ p ∈ lInf.val ∧ p ≠ A.rowInf ∧ p ≠ A.colInf
    simp only [S, Finset.mem_erase]
    tauto
  let e : SlopePoint A ≃ ↥S :=
    { toFun := fun p => ⟨p.val, (hs _).mpr p.property⟩
      invFun := fun p => ⟨p.val, (hs _).mp p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcol : A.colInf ∈ lInf.val.erase A.rowInf :=
    Finset.mem_erase.mpr ⟨A.rows_ne_cols.symm, A.col_mem⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  dsimp only [S]
  rw [Finset.card_erase_of_mem hcol, Finset.card_erase_of_mem A.row_mem, lInf.property.1]

private def slopePointSign (p : SlopePoint A) : Bool :=
  (affineQuartetGraph round closed cover A p.property.1 p.property.2.1 p.property.2.2
    (affineQuartetDirectionEquiv round closed cover lInf p.property.1 0)).positive

private def slopePointEquiv : SlopePoint A ≃ Bool := by
  let sign := slopePointSign round closed cover A
  have hinj : Function.Injective sign := by
    intro p q he
    by_contra hn
    have hpq : p.val ≠ q.val := fun he => hn (Subtype.ext he)
    exact (affineQuartetGraph_different_directions round closed cover p.property.1 q.property.1 hpq
      (affineQuartetGraph round closed cover A p.property.1 p.property.2.1 p.property.2.2
        (affineQuartetDirectionEquiv round closed cover lInf p.property.1 0))
      (affineQuartetGraph round closed cover A q.property.1 q.property.2.1 q.property.2.2
        (affineQuartetDirectionEquiv round closed cover lInf q.property.1 0))) he
  letI : Fintype (SlopePoint A) := Fintype.ofFinite _
  let label : Bool ≃ SlopePoint A := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card (α := SlopePoint A), slope_point_card]
    decide)
  have hs : Function.Surjective (sign ∘ label) :=
    Finite.surjective_of_injective (hinj.comp label.injective)
  refine Equiv.ofBijective sign ⟨hinj, fun t => ?_⟩
  obtain ⟨b, hb⟩ := hs t
  exact ⟨label b, hb⟩

private def ptAtSlope (s : Bool) : SlopePoint A := (slopePointEquiv round closed cover A).symm s

private theorem ptAtSlope_sign (s : Bool) :
    slopePointSign round closed cover A (ptAtSlope round closed cover A s) = s :=
  (slopePointEquiv round closed cover A).apply_symm_apply s

private def slopeLine (s : Bool) (b : ZMod 3) :
    AffineQuartetDirection (h := h) (system := system) lInf (ptAtSlope round closed cover A s).val :=
  let p := ptAtSlope round closed cover A s
  (affineQuartetOffsetEquiv round closed cover A p.property.1 p.property.2.1 p.property.2.2).symm b

private theorem slopeLine_mem_iff (s : Bool) (b x y : ZMod 3) :
    (A.pointEquiv round closed cover (x, y)).val ∈ (slopeLine round closed cover A s b).val ↔
      y = quartetSlope s x + b := by
  let p := ptAtSlope round closed cover A s
  let G L := affineQuartetGraph round closed cover A p.property.1 p.property.2.1 p.property.2.2 L
  let B := slopeLine round closed cover A s b
  let E := affineQuartetOffsetEquiv round closed cover A p.property.1 p.property.2.1 p.property.2.2
  have hB : E B = b := E.apply_symm_apply b
  have hb : (G B).offset = b := hB
  have hs : (G B).positive = s := by
    have hdir := affineQuartetGraph_same_direction round closed cover p.property.1
      (G B) (G (affineQuartetDirectionEquiv round closed cover lInf p.property.1 0))
    exact hdir.trans (ptAtSlope_sign round closed cover A s)
  change _ ↔ _
  rw [(G B).mem_iff, hs, hb]

private def coordinatePoint : PGThreePoint → Fin 13
  | .affine x y => (A.pointEquiv round closed cover (x, y)).val
  | .rowInfinity => A.rowInf
  | .colInfinity => A.colInf
  | .slopeInfinity s => (ptAtSlope round closed cover A s).val

private def coordinateLine : PGThreeLine → PlaneQuartetLine h system
  | .infinity => lInf
  | .row a => (A.rows a).val
  | .col b => (A.cols b).val
  | .slope s b => (slopeLine round closed cover A s b).val

private theorem coordinatePoint_surjective :
    Function.Surjective (coordinatePoint round closed cover A) := by
  intro p
  by_cases hp : p ∈ lInf
  · by_cases hpr : p = A.rowInf
    · exact ⟨.rowInfinity, hpr.symm⟩
    by_cases hpc : p = A.colInf
    · exact ⟨.colInfinity, hpc.symm⟩
    · let P : SlopePoint A := ⟨p, hp, hpr, hpc⟩
      let e := slopePointEquiv round closed cover A
      refine ⟨.slopeInfinity (e P), ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply P)
  · obtain ⟨⟨x, y⟩, hxy⟩ := (A.pointEquiv round closed cover).surjective ⟨p, hp⟩
    exact ⟨.affine x y, congrArg Subtype.val hxy⟩

private theorem coordinatePoint_injective :
    Function.Injective (coordinatePoint round closed cover A) := by
  let e : Fin 13 ≃ PGThreePoint := Fintype.equivOfCardEq (by simp [pgThreePoint_card])
  exact (Finite.injective_iff_surjective_of_equiv e.symm).mpr
    (coordinatePoint_surjective round closed cover A)

include round closed in
private theorem on_affine_line_at_infinity {p : Fin 13} (hp : p ∈ lInf)
    (L : AffineQuartetDirection (h := h) (system := system) lInf p)
    {q : Fin 13} (hq : q ∈ lInf) :
    q ∈ L.val ↔ q = p := by
  constructor
  · intro hqL
    exact affineQuartet_infinityPoint_unique round closed L.property.2
      hq hp hqL L.property.1
  · rintro rfl
    exact L.property.1

private theorem coordinate_incidence (p : PGThreePoint) (B : PGThreeLine) :
    coordinatePoint round closed cover A p ∈ coordinateLine round closed cover A B ↔ pgThreeIncidence p B := by
  let e := slopePointEquiv round closed cover A
  have hpt (s t : Bool) :
      (ptAtSlope round closed cover A s).val = (ptAtSlope round closed cover A t).val ↔ s = t := by
    constructor
    · intro he
      exact e.symm.injective (Subtype.ext he)
    · rintro rfl
      rfl
  cases B with
  | infinity =>
      cases p with
      | affine x y => exact iff_false_intro (A.pointEquiv round closed cover (x, y)).property
      | rowInfinity => exact iff_true_intro A.row_mem
      | colInfinity => exact iff_true_intro A.col_mem
      | slopeInfinity s => exact iff_true_intro (ptAtSlope round closed cover A s).property.1
  | row a =>
      cases p with
      | affine x y => exact A.point_mem_row_iff round closed cover x y a
      | rowInfinity => exact iff_true_intro (A.rows a).property.1
      | colInfinity =>
          exact iff_false_intro (fun he => A.rows_ne_cols
            (((on_affine_line_at_infinity round closed A.row_mem (A.rows a) A.col_mem).mp he).symm))
      | slopeInfinity s =>
          let pt := ptAtSlope round closed cover A s
          exact iff_false_intro (fun he => pt.property.2.1
            ((on_affine_line_at_infinity round closed A.row_mem (A.rows a) pt.property.1).mp he))
  | col b =>
      cases p with
      | affine x y => exact A.point_mem_col_iff round closed cover x y b
      | rowInfinity =>
          exact iff_false_intro (fun he => A.rows_ne_cols
            ((on_affine_line_at_infinity round closed A.col_mem (A.cols b) A.row_mem).mp he))
      | colInfinity => exact iff_true_intro (A.cols b).property.1
      | slopeInfinity s =>
          let pt := ptAtSlope round closed cover A s
          exact iff_false_intro (fun he => pt.property.2.2
            ((on_affine_line_at_infinity round closed A.col_mem (A.cols b) pt.property.1).mp he))
  | slope t b =>
      let pt := ptAtSlope round closed cover A t
      let L := slopeLine round closed cover A t b
      cases p with
      | affine x y => exact slopeLine_mem_iff round closed cover A t b x y
      | rowInfinity =>
          exact iff_false_intro (fun he => pt.property.2.1
            (((on_affine_line_at_infinity round closed pt.property.1 L A.row_mem).mp he).symm))
      | colInfinity =>
          exact iff_false_intro (fun he => pt.property.2.2
            (((on_affine_line_at_infinity round closed pt.property.1 L A.col_mem).mp he).symm))
      | slopeInfinity s =>
          exact (on_affine_line_at_infinity round closed pt.property.1 L
            (ptAtSlope round closed cover A s).property.1).trans (hpt s t)

private theorem coordinateLine_injective :
    Function.Injective (coordinateLine round closed cover A) := by
  intro B D he
  apply pgThreeLine_eq_of_incidence B D
  intro p
  rw [← coordinate_incidence round closed cover A, ← coordinate_incidence round closed cover A, he]

include round closed cover in
private theorem quartetLine_card :
    Nat.card (PlaneQuartetLine h system) = 13 := by
  let S := planeQuartets h system
  have hs (B : Finset (Fin 13)) : B ∈ S ↔ IsPlaneQuartet h system B := by simp [S, planeQuartets]
  let e : PlaneQuartetLine h system ≃ ↥S :=
    { toFun := fun B => ⟨B.val, (hs _).mpr B.property⟩
      invFun := fun B => ⟨B.val, (hs _).mp B.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact planeQuartets_card round closed cover

private theorem coordinateLine_surjective :
    Function.Surjective (coordinateLine round closed cover A) := by
  cases nonempty_fintype (PlaneQuartetLine h system)
  let e : PlaneQuartetLine h system ≃ PGThreeLine := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card (α := PlaneQuartetLine h system), quartetLine_card round closed cover, pgThreeLine_card])
  exact (Finite.injective_iff_surjective_of_equiv e.symm).mp
    (coordinateLine_injective round closed cover A)

include round closed cover in
/-- The actual closed quartets of a quartet-covered thirteen-plane system are the lines
of PG(2,3), with an incidence-preserving bijection on points and lines. -/
/- The paper uses uniqueness of the order-three projective plane, as treated by Marshall
Hall, Jr., Combinatorial Theory (1986), and D. R. Hughes and F. C. Piper, Projective
Planes (1973). Here affine coordinates give an explicit incidence isomorphism with
PG(2,3). -/
theorem thirteenPlane_quartets_isomorphic_pgThree :
    ∃ p : PGThreePoint ≃ Fin 13, ∃ L : PGThreeLine ≃ PlaneQuartetLine h system,
      ∀ x B, p x ∈ L B ↔ pgThreeIncidence x B := by
  obtain ⟨B, hB, h₀, h₁⟩ := cover 0 1 (by decide)
  let lInf' : PlaneQuartetLine h system := ⟨B, hB⟩
  let axes : QuartetAffineAxes (h := h) (system := system) lInf' :=
    { rowInf := 0
      colInf := 1
      row_mem := h₀
      col_mem := h₁
      rows_ne_cols := by decide
      rows := affineQuartetDirectionEquiv round closed cover lInf' h₀
      cols := affineQuartetDirectionEquiv round closed cover lInf' h₁ }
  refine ⟨Equiv.ofBijective (coordinatePoint round closed cover axes)
    ⟨coordinatePoint_injective round closed cover axes, coordinatePoint_surjective round closed cover axes⟩,
    Equiv.ofBijective (coordinateLine round closed cover axes)
    ⟨coordinateLine_injective round closed cover axes, coordinateLine_surjective round closed cover axes⟩,
    coordinate_incidence round closed cover axes⟩

/-- Quartet coverage is equivalent to the actual quartet incidence being that of PG(2,3).
This is the thirteen-plane support and incidence theorem (ii)(c) iff (d), including the explicit incidence isomorphism. -/
theorem thirteenPlane_quartet_cover_iff_pgThree (round : IsRound h c)
    (closed : IsClosedPlaneSystem h system) :
    (∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B) ↔
    ∃ p : PGThreePoint ≃ Fin 13, ∃ L : PGThreeLine ≃ PlaneQuartetLine h system,
      ∀ x B, p x ∈ L B ↔ pgThreeIncidence x B := by
  constructor
  · exact thirteenPlane_quartets_isomorphic_pgThree round closed
  · rintro ⟨p, L, hinc⟩ i j hij
    have hn : p.symm i ≠ p.symm j := p.symm.injective.ne hij
    obtain ⟨B, hi, hj⟩ := pgThree_pair_has_line _ _ hn
    have hi' := (hinc (p.symm i) B).mpr hi
    have hj' := (hinc (p.symm j) B).mpr hj
    rw [p.apply_symm_apply] at hi' hj'
    exact ⟨(L B).val, (L B).property, hi', hj'⟩

/-- Quartet coverage is also equivalent to the standard projective-plane axioms and exact order. -/
theorem thirteenPlane_quartet_cover_iff_projective (round : IsRound h c)
    (closed : IsClosedPlaneSystem h system) :
    (∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B) ↔
    ∃ P : Configuration.ProjectivePlane (Fin 13) (PlaneQuartetLine h system),
      @Configuration.ProjectivePlane.order (Fin 13) (PlaneQuartetLine h system) _ P = 3 := by
  constructor
  · intro cover
    exact ⟨planeQuartets_projectivePlane round closed cover,
      planeQuartets_projectivePlane_order round closed cover⟩
  · rintro ⟨P, _⟩ i j hij
    obtain ⟨L, hL, _⟩ := @Configuration.HasLines.existsUnique_line (Fin 13)
      (PlaneQuartetLine h system) _ P.toHasLines i j hij
    exact ⟨L.val, L.property, hL.1, hL.2⟩

/-- For any incidence isomorphism with PG(2,3), the shares are exactly the indicators
of collinearity among the distinct projective points. -/
theorem thirteenPlane_share_eq_pgThree_collinearity (round : IsRound h c)
    (closed : IsClosedPlaneSystem h system)
    (p : PGThreePoint ≃ Fin 13) (L : PGThreeLine ≃ PlaneQuartetLine h system)
    (iso : ∀ x B, p x ∈ L B ↔ pgThreeIncidence x B)
    {x y z : PGThreePoint} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    planeShare h system (p x) (p y) (p z) =
      (if ∃ B : PGThreeLine, pgThreeIncidence x B ∧ pgThreeIncidence y B ∧ pgThreeIncidence z B
        then 1 else 0) := by
  have cover := (thirteenPlane_quartet_cover_iff_pgThree round closed).mpr ⟨p, L, iso⟩
  rw [planeShare_binary_of_quartet_cover round closed cover
    (p.injective.ne hxy) (p.injective.ne hzx) (p.injective.ne hzy)]
  have he : (∃ B, IsPlaneQuartet h system B ∧ p x ∈ B ∧ p y ∈ B ∧ p z ∈ B) ↔
      ∃ B : PGThreeLine, pgThreeIncidence x B ∧ pgThreeIncidence y B ∧ pgThreeIncidence z B := by
    constructor
    · rintro ⟨B, hB, hx, hy, hz⟩
      let b : PlaneQuartetLine h system := ⟨B, hB⟩
      refine ⟨L.symm b, (iso x _).mp ?_, (iso y _).mp ?_, (iso z _).mp ?_⟩
      · rw [L.apply_symm_apply]
        change p x ∈ B
        exact hx
      · rw [L.apply_symm_apply]
        change p y ∈ B
        exact hy
      · rw [L.apply_symm_apply]
        change p z ∈ B
        exact hz
    · rintro ⟨B, hx, hy, hz⟩
      exact ⟨(L B).val, (L B).property, (iso x B).mpr hx, (iso y B).mpr hy, (iso z B).mpr hz⟩
  simp only [he]

end
end ThirteenPlanes.RoundCubics
