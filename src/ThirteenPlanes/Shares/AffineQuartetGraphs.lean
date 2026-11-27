module

public import ThirteenPlanes.Shares.AffineQuartetChart

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin 13)}

/-- A choice of two points at infinity and a labeling of their three parallel lines. -/
structure QuartetAffineAxes (lInf : PlaneQuartetLine h system) where
  rowInf : Fin 13
  colInf : Fin 13
  row_mem : rowInf ∈ lInf
  col_mem : colInf ∈ lInf
  rows_ne_cols : rowInf ≠ colInf
  rows : ZMod 3 ≃ AffineQuartetDirection (h := h) (system := system) lInf rowInf
  cols : ZMod 3 ≃ AffineQuartetDirection (h := h) (system := system) lInf colInf

variable (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
  (cover : ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)
  {lInf : PlaneQuartetLine h system} (A : QuartetAffineAxes (h := h) (system := system) lInf)

def QuartetAffineAxes.pointEquiv : (ZMod 3 × ZMod 3) ≃ AffineQuartetPoint (h := h) (system := system) lInf :=
  affineQuartetPointEquiv round closed cover A.row_mem A.col_mem A.rows_ne_cols A.rows A.cols

include round closed cover in
theorem QuartetAffineAxes.point_mem_axes (a b : ZMod 3) :
    ((A.pointEquiv round closed cover (a, b)).val ∈ (A.rows a).val) ∧
      ((A.pointEquiv round closed cover (a, b)).val ∈ (A.cols b).val) :=
  affineQuartetPointEquiv_mem round closed cover A.row_mem A.col_mem A.rows_ne_cols A.rows A.cols a b

include round closed cover in
theorem QuartetAffineAxes.point_mem_row_iff (a b i : ZMod 3) :
    (A.pointEquiv round closed cover (a, b)).val ∈ (A.rows i).val ↔ a = i := by
  constructor
  · intro hx
    obtain ⟨row, _, hu⟩ := affineQuartet_existsUnique_direction_line round closed cover A.row_mem
      (A.pointEquiv round closed cover (a, b))
    exact A.rows.injective ((hu _ (A.point_mem_axes round closed cover a b).1).trans (hu _ hx).symm)
  · rintro rfl
    exact (A.point_mem_axes round closed cover a b).1

include round closed cover in
theorem QuartetAffineAxes.point_mem_col_iff (a b j : ZMod 3) :
    (A.pointEquiv round closed cover (a, b)).val ∈ (A.cols j).val ↔ b = j := by
  constructor
  · intro hx
    obtain ⟨col, _, hu⟩ := affineQuartet_existsUnique_direction_line round closed cover A.col_mem
      (A.pointEquiv round closed cover (a, b))
    exact A.cols.injective ((hu _ (A.point_mem_axes round closed cover a b).2).trans (hu _ hx).symm)
  · rintro rfl
    exact (A.point_mem_axes round closed cover a b).2

private theorem permutation_of_three_affine :
    ∀ a b d : ZMod 3, a ≠ b → a ≠ d → b ≠ d →
      ∃ positive : Bool, b = quartetSlope positive 1 + a ∧
        d = quartetSlope positive 2 + a := by
  decide

private theorem zmod3_values : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide

private theorem affine_permutation (f : ZMod 3 → ZMod 3) (hf : Function.Injective f) :
    ∃ positive : Bool, ∃ offset : ZMod 3, ∀ x, f x = quartetSlope positive x + offset := by
  obtain ⟨s, h₁, h₂⟩ := permutation_of_three_affine (f 0) (f 1) (f 2)
    (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide))
  refine ⟨s, f 0, fun x => ?_⟩
  rcases zmod3_values x with rfl | rfl | rfl
  · cases s <;> simp [quartetSlope]
  · exact h₁
  · exact h₂

section Graph

variable {p : Fin 13} (hp : p ∈ lInf) (hpr : p ≠ A.rowInf) (hpc : p ≠ A.colInf)
  (L : AffineQuartetDirection (h := h) (system := system) lInf p)

include round closed cover hp hpr hpc in
/-- Every line in one of the other two parallel classes is the graph of a permutation of
the three affine coordinates, hence has slope 1 or −1. -/
theorem affineQuartet_affineGraph :
    ∃ s : Bool, ∃ b : ZMod 3,
      ∀ x y : ZMod 3, (A.pointEquiv round closed cover (x, y)).val ∈ L.val ↔
        y = quartetSlope s x + b := by
  let e := A.pointEquiv round closed cover
  let pointOnLine (x : ZMod 3) : AffineQuartetPoint (h := h) (system := system) lInf :=
    (affineQuartet_existsUnique_intersection round closed cover A.row_mem hp hpr.symm (A.rows x) L)
      |>.exists.choose
  have point_mem (x : ZMod 3) : (pointOnLine x).val ∈ (A.rows x).val ∧ (pointOnLine x).val ∈ L.val :=
    (affineQuartet_existsUnique_intersection round closed cover A.row_mem hp hpr.symm (A.rows x) L)
      |>.exists.choose_spec
  let f (x : ZMod 3) := (e.symm (pointOnLine x)).2
  have eq_coord (x : ZMod 3) : e (x, f x) = pointOnLine x := by
    have hp' := (point_mem x).1
    rw [← e.apply_symm_apply (pointOnLine x)] at hp' ⊢
    let ab := e.symm (pointOnLine x)
    change (A.pointEquiv round closed cover (ab.1, ab.2)).val ∈ (A.rows x).val at hp'
    change e (x, ab.2) = e ab
    exact congrArg e (Prod.ext ((A.point_mem_row_iff round closed cover ..).mp hp').symm rfl)
  have graph (x y : ZMod 3) : (e (x, y)).val ∈ L.val ↔ y = f x := by
    constructor
    · intro hxy
      obtain ⟨z, _, hu⟩ := affineQuartet_existsUnique_intersection round closed cover A.row_mem hp
        hpr.symm (A.rows x) L
      have hxy' := hu (e (x, y)) ⟨(A.point_mem_axes round closed cover x y).1, hxy⟩
      have hx' := hu (pointOnLine x) (point_mem x)
      have hpair := e.injective (hxy'.trans (hx'.symm.trans (eq_coord x).symm))
      exact congrArg Prod.snd hpair
    · rintro rfl
      rw [eq_coord]
      exact (point_mem x).2
  have hf : Function.Injective f := by
    intro x y he
    obtain ⟨z, _, hu⟩ := affineQuartet_existsUnique_intersection round closed cover A.col_mem hp
      hpc.symm (A.cols (f x)) L
    have hx : e (x, f x) = z := hu _ ⟨(A.point_mem_axes round closed cover x (f x)).2,
      (graph x (f x)).mpr rfl⟩
    have hy : e (y, f x) = z := hu _ ⟨(A.point_mem_axes round closed cover y (f x)).2,
      (graph y (f x)).mpr he⟩
    exact congrArg Prod.fst (e.injective (hx.trans hy.symm))
  obtain ⟨s, b, hsb⟩ := affine_permutation f hf
  exact ⟨s, b, fun x y => by rw [← hsb]; exact graph x y⟩

/-- The graph coordinates of a line in a non-axis direction of the chart. -/
structure AffineQuartetGraph where
  positive : Bool
  offset : ZMod 3
  mem_iff : ∀ x y : ZMod 3, (A.pointEquiv round closed cover (x, y)).val ∈ L.val ↔
    y = quartetSlope positive x + offset

def affineQuartetGraph : AffineQuartetGraph round closed cover A L := by
  let existsGraph := affineQuartet_affineGraph round closed cover A hp hpr hpc L
  exact ⟨existsGraph.choose, existsGraph.choose_spec.choose, existsGraph.choose_spec.choose_spec⟩

end Graph

private theorem quartetSlope_one_injective :
    Function.Injective (fun s : Bool => quartetSlope s 1) := by
  change ∀ a b : Bool, quartetSlope a 1 = quartetSlope b 1 → a = b
  decide

private theorem opposite_slopes_cross :
    ∀ s t : Bool, s ≠ t → ∀ b d : ZMod 3, ∃ x, quartetSlope s x + b = quartetSlope t x + d := by
  decide

variable {A}

include round closed cover in
private theorem graph_parameters_eq_of_same_line
    {p q : Fin 13} {L : AffineQuartetDirection (h := h) (system := system) lInf p} {M : AffineQuartetDirection (h := h) (system := system) lInf q}
    (G : AffineQuartetGraph round closed cover A L) (H : AffineQuartetGraph round closed cover A M)
    (sameLine : L.val = M.val) :
    G.positive = H.positive ∧ G.offset = H.offset := by
  have h (x : ZMod 3) : quartetSlope G.positive x + G.offset = quartetSlope H.positive x + H.offset := by
    have hx := (G.mem_iff x _).mpr rfl
    rw [sameLine] at hx
    exact (H.mem_iff x _).mp hx
  have h₀ : G.offset = H.offset := by simpa using h 0
  have h₁ := h 1
  rw [h₀] at h₁
  exact ⟨quartetSlope_one_injective (add_right_cancel h₁), h₀⟩

include round closed in
private theorem same_line_of_graph_parameters_eq
    {p q : Fin 13} {L : AffineQuartetDirection (h := h) (system := system) lInf p} {M : AffineQuartetDirection (h := h) (system := system) lInf q}
    (G : AffineQuartetGraph round closed cover A L) (H : AffineQuartetGraph round closed cover A M)
    (hs : G.positive = H.positive) (hb : G.offset = H.offset) :
    L.val = M.val := by
  let e := A.pointEquiv round closed cover
  let x := e (0, G.offset)
  let y := e (1, quartetSlope G.positive 1 + G.offset)
  have hxL : x.val ∈ L.val := (G.mem_iff ..).mpr (by simp)
  have hyL : y.val ∈ L.val := (G.mem_iff ..).mpr rfl
  have hxM : x.val ∈ M.val := (H.mem_iff ..).mpr (by simp [← hb])
  have hyM : y.val ∈ M.val := (H.mem_iff ..).mpr (by rw [← hs, ← hb])
  have hxy : x.val ≠ y.val := by
    intro he
    have hpair := e.injective (Subtype.ext he)
    have hzero : (0 : ZMod 3) = 1 := congrArg Prod.fst hpair
    exact (by decide : (0 : ZMod 3) ≠ 1) hzero
  exact Subtype.ext (planeQuartet_unique_through_pair round closed L.val.property M.val.property
    hxy hxL hyL hxM hyM)

include round closed cover in
theorem affineQuartetGraph_same_direction
    {p : Fin 13} (hp : p ∈ lInf) {L M : AffineQuartetDirection (h := h) (system := system) lInf p}
    (G : AffineQuartetGraph round closed cover A L) (H : AffineQuartetGraph round closed cover A M) :
    G.positive = H.positive := by
  by_contra hne
  obtain ⟨x, hx⟩ := opposite_slopes_cross G.positive H.positive hne G.offset H.offset
  let y := quartetSlope G.positive x + G.offset
  let pt := A.pointEquiv round closed cover (x, y)
  have hL : pt.val ∈ L.val := (G.mem_iff x y).mpr rfl
  have hM : pt.val ∈ M.val := (H.mem_iff x y).mpr hx
  obtain ⟨_, _, hu⟩ := affineQuartet_existsUnique_direction_line round closed cover hp pt
  have hLM := (hu _ hL).trans (hu _ hM).symm
  exact hne (graph_parameters_eq_of_same_line round closed cover G H (congrArg Subtype.val hLM)).1

include round closed cover in
theorem affineQuartetGraph_different_directions
    {p q : Fin 13} (hp : p ∈ lInf) (hq : q ∈ lInf) (hpq : p ≠ q)
    {L : AffineQuartetDirection (h := h) (system := system) lInf p} {M : AffineQuartetDirection (h := h) (system := system) lInf q}
    (G : AffineQuartetGraph round closed cover A L) (H : AffineQuartetGraph round closed cover A M) :
    G.positive ≠ H.positive := by
  intro he
  obtain ⟨pt, ⟨hL, hM⟩, _⟩ := affineQuartet_existsUnique_intersection round closed cover hp hq hpq L M
  obtain ⟨⟨x, y⟩, rfl⟩ := (A.pointEquiv round closed cover).surjective pt
  have h₁ := (G.mem_iff x y).mp hL
  have h₂ := (H.mem_iff x y).mp hM
  rw [he] at h₁
  have hb := add_left_cancel (h₁.symm.trans h₂)
  have hl := same_line_of_graph_parameters_eq round closed cover G H he hb
  exact hpq (affineQuartet_infinityPoint_unique round closed L.property.2
    hp hq L.property.1 (hl ▸ M.property.1))

/-- The lines of either non-axis direction are labeled bijectively by their constant term. -/
def affineQuartetOffsetEquiv (A : QuartetAffineAxes (h := h) (system := system) lInf)
    {p : Fin 13} (hp : p ∈ lInf) (hpr : p ≠ A.rowInf) (hpc : p ≠ A.colInf) :
    AffineQuartetDirection (h := h) (system := system) lInf p ≃ ZMod 3 := by
  let offset (L : AffineQuartetDirection (h := h) (system := system) lInf p) :=
    (affineQuartetGraph round closed cover A hp hpr hpc L).offset
  have ho : Function.Injective offset := by
    intro L M he
    let G := affineQuartetGraph round closed cover A hp hpr hpc L
    let H := affineQuartetGraph round closed cover A hp hpr hpc M
    exact Subtype.ext (same_line_of_graph_parameters_eq round closed cover G H
      (affineQuartetGraph_same_direction round closed cover hp G H) he)
  let e := affineQuartetDirectionEquiv round closed cover lInf hp
  have hs : Function.Surjective (offset ∘ e) :=
    Finite.surjective_of_injective (ho.comp e.injective)
  have honto : Function.Surjective offset := fun b => by
    obtain ⟨x, hx⟩ := hs b
    exact ⟨e x, hx⟩
  exact Equiv.ofBijective offset ⟨ho, honto⟩

@[simp] theorem affineQuartetOffsetEquiv_apply (A : QuartetAffineAxes (h := h) (system := system) lInf)
    {p : Fin 13} (hp : p ∈ lInf) (hpr : p ≠ A.rowInf) (hpc : p ≠ A.colInf)
    (L : AffineQuartetDirection (h := h) (system := system) lInf p) :
    affineQuartetOffsetEquiv round closed cover A hp hpr hpc L =
      (affineQuartetGraph round closed cover A hp hpr hpc L).offset := rfl

end
end ThirteenPlanes.RoundCubics
