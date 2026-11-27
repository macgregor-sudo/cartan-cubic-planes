module

public import ThirteenPlanes.Shares.ProjectiveQuartets
public import Mathlib.Data.ZMod.Basic

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin 13)}

local notation "Line" => PlaneQuartetLine h system

/-- Affine lines in a parallel class are exactly the quartets through its point at infinity,
apart from the chosen line at infinity itself. -/
abbrev AffineQuartetDirection (lInf : Line) (p : Fin 13) := {L : Line // p ∈ L ∧ L ≠ lInf}

/-- Points of the affine chart are those outside the deleted quartet. -/
abbrev AffineQuartetPoint (lInf : Line) := {p : Fin 13 // p ∉ lInf}

private theorem direction_card
    (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    (cover : ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)
    (lInf : Line) {p : Fin 13} (hp : p ∈ lInf) :
    Nat.card (AffineQuartetDirection lInf p) = 3 := by
  let s := (planeQuartetsThrough h system p).erase lInf.val
  have hs (B : Finset (Fin 13)) :
      B ∈ s ↔ B ≠ lInf.val ∧ IsPlaneQuartet h system B ∧ p ∈ B := by
    simp [s, planeQuartetsThrough, planeQuartets]
  have hsInf : lInf.val ∈ planeQuartetsThrough h system p := by
    have hmem : p ∈ lInf.val := hp
    simp [planeQuartetsThrough, planeQuartets, hmem, lInf.property]
  let he : AffineQuartetDirection lInf p ≃ ↥s :=
    { toFun := fun L => ⟨L.val.val, (hs _).mpr ⟨fun he => L.property.2 (Subtype.ext he),
        L.val.property, L.property.1⟩⟩
      invFun := fun B => ⟨⟨B.val, ((hs _).mp B.property).2.1⟩, ((hs _).mp B.property).2.2,
        fun he => ((hs _).mp B.property).1 (congrArg Subtype.val he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_coe,
    show s.card = 3 from by
      rw [Finset.card_erase_of_mem hsInf, planeQuartets_through_point_card round closed cover]]

/-- A parallel class has exactly three lines, indexed by the three elements of the prime field. -/
def affineQuartetDirectionEquiv
    (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
    (cover : ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)
    (lInf : Line) {p : Fin 13} (hp : p ∈ lInf) :
    ZMod 3 ≃ AffineQuartetDirection lInf p := by
  letI : Fintype (AffineQuartetDirection lInf p) := Fintype.ofFinite _
  exact Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card (α := AffineQuartetDirection lInf p),
      direction_card round closed cover lInf hp]
    decide)

variable (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
  (cover : ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)

include round closed in
theorem affineQuartet_infinityPoint_unique {lInf L : Line} (hL : L ≠ lInf)
    {p q : Fin 13} (hpInf : p ∈ lInf) (hqInf : q ∈ lInf) (hp : p ∈ L) (hq : q ∈ L) : p = q := by
  by_contra hn
  exact hL (Subtype.ext (planeQuartet_unique_through_pair round closed L.property lInf.property
    hn hp hq hpInf hqInf))

include round closed cover in
theorem affineQuartet_existsUnique_infinityPoint {lInf L : Line} (hL : L ≠ lInf) :
    ∃! p : Fin 13, p ∈ lInf ∧ p ∈ L :=
  planeQuartets_existsUnique_intersection round closed cover lInf.property L.property
    (fun he => hL (Subtype.ext he.symm))

include round closed cover in
theorem affineQuartet_existsUnique_direction_line {lInf : Line} {p : Fin 13} (hp : p ∈ lInf)
    (x : AffineQuartetPoint lInf) :
    ∃! L : AffineQuartetDirection lInf p, x.val ∈ L.val := by
  have hpx : p ≠ x.val := fun he => x.property (he ▸ hp)
  obtain ⟨B, hB, hpB, hxB⟩ := cover p x.val hpx
  let L : Line := ⟨B, hB⟩
  have hne : L ≠ lInf := fun he => x.property (he ▸ (show x.val ∈ L from hxB))
  refine ⟨⟨L, hpB, hne⟩, hxB, fun D hD => ?_⟩
  exact Subtype.ext (Subtype.ext
    (planeQuartet_unique_through_pair round closed D.val.property hB
      hpx D.property.1 hD hpB hxB))

include round closed cover in
theorem affineQuartet_existsUnique_intersection {lInf : Line} {p q : Fin 13}
    (hp : p ∈ lInf) (hq : q ∈ lInf) (hpq : p ≠ q)
    (B : AffineQuartetDirection lInf p) (D : AffineQuartetDirection lInf q) :
    ∃! x : AffineQuartetPoint lInf, x.val ∈ B.val ∧ x.val ∈ D.val := by
  have hBD : B.val.val ≠ D.val.val := by
    intro he
    have he' : B.val = D.val := Subtype.ext he
    exact hpq (affineQuartet_infinityPoint_unique round closed B.property.2
      hp hq B.property.1 (he' ▸ D.property.1))
  obtain ⟨x, hx, hu⟩ :=
    planeQuartets_existsUnique_intersection round closed cover B.val.property D.val.property hBD
  have hxInf : x ∉ lInf := by
    intro h
    have hxp := affineQuartet_infinityPoint_unique round closed B.property.2 h hp hx.1 B.property.1
    have hxq := affineQuartet_infinityPoint_unique round closed D.property.2 h hq hx.2 D.property.1
    exact hpq (hxp.symm.trans hxq)
  exact ⟨⟨x, hxInf⟩, hx, fun y hy => Subtype.ext (hu _ hy)⟩

/-- Two distinct parallel classes give the nine affine points their coordinates in the
cartesian square of the three-element field. -/
def affineQuartetPointEquiv {lInf : Line} {p q : Fin 13}
    (hp : p ∈ lInf) (hq : q ∈ lInf) (hpq : p ≠ q)
    (rows : ZMod 3 ≃ AffineQuartetDirection lInf p)
    (cols : ZMod 3 ≃ AffineQuartetDirection lInf q) :
    (ZMod 3 × ZMod 3) ≃ AffineQuartetPoint lInf := by
  let through {r : Fin 13} (hr : r ∈ lInf) (x : AffineQuartetPoint lInf) :
      AffineQuartetDirection lInf r :=
    (affineQuartet_existsUnique_direction_line round closed cover hr x).exists.choose
  have through_mem {r : Fin 13} (hr : r ∈ lInf) (x : AffineQuartetPoint lInf) : x.val ∈ (through hr x).val :=
    (affineQuartet_existsUnique_direction_line round closed cover hr x).exists.choose_spec
  have through_eq {r : Fin 13} (hr : r ∈ lInf) (x : AffineQuartetPoint lInf)
      (L : AffineQuartetDirection lInf r) (hx : x.val ∈ L.val) : through hr x = L := by
    obtain ⟨B, _, hu⟩ := affineQuartet_existsUnique_direction_line round closed cover hr x
    exact (hu _ (through_mem hr x)).trans (hu _ hx).symm
  let coord (a b : ZMod 3) :=
    (affineQuartet_existsUnique_intersection round closed cover hp hq hpq (rows a) (cols b))
      |>.exists.choose
  have coord_mem (a b : ZMod 3) :
      (coord a b).val ∈ (rows a).val ∧ (coord a b).val ∈ (cols b).val :=
    (affineQuartet_existsUnique_intersection round closed cover hp hq hpq (rows a) (cols b))
      |>.exists.choose_spec
  have coord_eq (a b : ZMod 3) (x : AffineQuartetPoint lInf)
      (hx : x.val ∈ (rows a).val ∧ x.val ∈ (cols b).val) : coord a b = x := by
    obtain ⟨p, _, hu⟩ := affineQuartet_existsUnique_intersection round closed cover hp hq hpq (rows a) (cols b)
    exact (hu _ (coord_mem a b)).trans (hu _ hx).symm
  refine ⟨fun ab => coord ab.1 ab.2, fun x => (rows.symm (through hp x), cols.symm (through hq x)), ?_, ?_⟩
  · intro ab
    change (rows.symm (through hp (coord ab.1 ab.2)), cols.symm (through hq (coord ab.1 ab.2))) = ab
    rw [through_eq hp _ _ (coord_mem ab.1 ab.2).1, through_eq hq _ _ (coord_mem ab.1 ab.2).2,
      rows.symm_apply_apply, cols.symm_apply_apply]
  · intro x
    apply coord_eq
    exact ⟨by rw [rows.apply_symm_apply]; exact through_mem hp x,
      by rw [cols.apply_symm_apply]; exact through_mem hq x⟩

theorem affineQuartetPointEquiv_mem {lInf : Line} {p q : Fin 13}
    (hp : p ∈ lInf) (hq : q ∈ lInf) (hpq : p ≠ q)
    (rows : ZMod 3 ≃ AffineQuartetDirection lInf p)
    (cols : ZMod 3 ≃ AffineQuartetDirection lInf q) (a b : ZMod 3) :
    ((affineQuartetPointEquiv round closed cover hp hq hpq rows cols (a, b)).val ∈ (rows a).val) ∧
      ((affineQuartetPointEquiv round closed cover hp hq hpq rows cols (a, b)).val ∈ (cols b).val) :=
  (affineQuartet_existsUnique_intersection round closed cover hp hq hpq (rows a) (cols b))
    |>.exists.choose_spec

/-- Positive and negative slopes in the affine plane over the three-element field. -/
def quartetSlope (positive : Bool) (x : ZMod 3) : ZMod 3 :=
  if positive then x else -x

@[simp] theorem quartetSlope_zero (s : Bool) : quartetSlope s 0 = 0 := by cases s <;> simp [quartetSlope]

end
end ThirteenPlanes.RoundCubics
