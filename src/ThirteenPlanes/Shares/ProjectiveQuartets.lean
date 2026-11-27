module

public import ThirteenPlanes.Shares.Incidence
public import Mathlib.Combinatorics.Configuration

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin 13)}

abbrev PlaneQuartetLine (h : SymmetricCubic V) (system : PlaneDecomposition V (Fin 13)) :=
  {B : Finset (Fin 13) // IsPlaneQuartet h system B}

instance : Membership (Fin 13) (PlaneQuartetLine h system) :=
  ⟨fun B p => p ∈ B.val⟩

variable (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
  (cover : ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)

include round closed cover in
private theorem line_notThrough_pair (p q : Fin 13) :
    ∃ B : PlaneQuartetLine h system, p ∉ B ∧ q ∉ B := by
  let P := planeQuartetsThrough h system p
  let Q := planeQuartetsThrough h system q
  have hp : P.card = 4 := planeQuartets_through_point_card round closed cover p
  have hq : Q.card = 4 := planeQuartets_through_point_card round closed cover q
  have hl := planeQuartets_card round closed cover
  have hbound := Finset.card_union_le P Q
  obtain ⟨B, hB, hpq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := P ∪ Q) (t := planeQuartets h system) (by omega)
  have hB' := (Finset.mem_filter.mp hB).2
  refine ⟨⟨B, hB'⟩, ?_, ?_⟩
  · exact fun hb => hpq (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hB, hb⟩))
  · exact fun hb => hpq (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hB, hb⟩))

omit [FiniteDimensional ℝ V] in
private theorem point_notOn_two_lines (B D : PlaneQuartetLine h system) :
    ∃ p : Fin 13, p ∉ B ∧ p ∉ D := by
  have hb := B.property.1
  have hd := D.property.1
  have h := Finset.card_union_le B.val D.val
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := B.val ∪ D.val) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
  exact ⟨p, fun h => hp (Finset.mem_union_left _ h), fun h => hp (Finset.mem_union_right _ h)⟩

/-- The actual closed quartets form a projective plane, whenever they cover all pairs.
The point type is the thirteen planes and the line type is the actual closed quartets. -/
@[instance_reducible]
def planeQuartets_projectivePlane : Configuration.ProjectivePlane (Fin 13) (PlaneQuartetLine h system) where
  exists_point B := by
    obtain ⟨p, hp, _⟩ := point_notOn_two_lines B B
    exact ⟨p, hp⟩
  exists_line p := by
    obtain ⟨B, hB, _⟩ := line_notThrough_pair round closed cover p p
    exact ⟨B, hB⟩
  eq_or_eq := by
    intro p q B D hpB hqB hpD hqD
    by_cases he : p = q
    · exact Or.inl he
    · exact Or.inr (Subtype.ext
        (planeQuartet_unique_through_pair round closed B.property D.property he hpB hqB hpD hqD))
  mkLine {p q} hpq := ⟨(cover p q hpq).choose, (cover p q hpq).choose_spec.1⟩
  mkLine_ax {p q} hpq := (cover p q hpq).choose_spec.2
  mkPoint {B D} hBD := (planeQuartets_existsUnique_intersection round closed cover
    B.property D.property (fun h => hBD (Subtype.ext h))).exists.choose
  mkPoint_ax {B D} hBD := (planeQuartets_existsUnique_intersection round closed cover
    B.property D.property (fun h => hBD (Subtype.ext h))).exists.choose_spec
  exists_config := by
    let p₂ : Fin 13 := 0
    let p₃ : Fin 13 := 1
    have h₂₃ : p₂ ≠ p₃ := by decide
    obtain ⟨B, hB, hp₂, hp₃⟩ := cover p₂ p₃ h₂₃
    let l₂ : PlaneQuartetLine h system := ⟨B, hB⟩
    obtain ⟨D, hD, hne⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {B}) (t := planeQuartetsThrough h system p₂) (by
        rw [planeQuartets_through_point_card round closed cover, Finset.card_singleton]
        decide)
    have hD' := Finset.mem_filter.mp hD
    let l₃ : PlaneQuartetLine h system := ⟨D, (Finset.mem_filter.mp hD'.1).2⟩
    have hnot : p₃ ∉ l₃ := by
      intro hp
      apply hne
      exact Finset.mem_singleton.mpr
        (planeQuartet_unique_through_pair round closed l₃.property hB h₂₃ hD'.2 hp hp₂ hp₃)
    obtain ⟨p₁, h₁₂, h₁₃⟩ := point_notOn_two_lines l₂ l₃
    obtain ⟨l₁, h₂₁, h₃₁⟩ := line_notThrough_pair round closed cover p₂ p₃
    exact ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, hp₂, hD'.2, h₃₁, hp₃, hnot⟩

/-- The projective plane of actual quartets has order three. -/
theorem planeQuartets_projectivePlane_order :
    @Configuration.ProjectivePlane.order (Fin 13) (PlaneQuartetLine h system) _
      (planeQuartets_projectivePlane round closed cover) = 3 := by
  let inst := planeQuartets_projectivePlane round closed cover
  obtain ⟨B, hB, _, _⟩ := cover 0 1 (by decide)
  let l : PlaneQuartetLine h system := ⟨B, hB⟩
  have hc : Configuration.pointCount (Fin 13) l = 4 := by
    change Nat.card {p : Fin 13 // p ∈ B} = 4
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hB.1]
  have hp := @Configuration.ProjectivePlane.pointCount_eq (Fin 13) _ _ inst _ _ l
  change @Configuration.ProjectivePlane.order (Fin 13) (PlaneQuartetLine h system) _ inst = 3
  omega

end
end ThirteenPlanes.RoundCubics
