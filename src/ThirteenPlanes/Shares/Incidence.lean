module

public import ThirteenPlanes.Shares.Quartets

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {c : ℝ} {h : SymmetricCubic V} {system : PlaneDecomposition V (Fin 13)}

def planeQuartets (h : SymmetricCubic V) (system : PlaneDecomposition V (Fin 13)) :
    Finset (Finset (Fin 13)) :=
  Finset.univ.filter (IsPlaneQuartet h system)

/-- The actual closed quartets incident with a fixed plane. -/
abbrev planeQuartetsThrough (h : SymmetricCubic V) (system : PlaneDecomposition V (Fin 13)) (p : Fin 13) :
    Finset (Finset (Fin 13)) :=
  (planeQuartets h system).filter (fun B => p ∈ B)

omit [FiniteDimensional ℝ V] in
private theorem throughPoint_mem {p : Fin 13} {B : Finset (Fin 13)} :
    B ∈ planeQuartetsThrough h system p ↔ IsPlaneQuartet h system B ∧ p ∈ B := by
  simp [planeQuartetsThrough, planeQuartets]

variable (round : IsRound h c) (closed : IsClosedPlaneSystem h system)
  (cover : ∀ i j : Fin 13, i ≠ j → ∃ B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B)

include round closed cover in
/-- In a quartet-covered thirteen-plane system, exactly four closed quartets meet each plane. -/
theorem planeQuartets_through_point_card (p : Fin 13) : (planeQuartetsThrough h system p).card = 4 := by
  let T := planeQuartetsThrough h system p
  have hunion : T.biUnion (fun B => B.erase p) = Finset.univ.erase p := by
    ext q
    constructor
    · intro hq
      obtain ⟨B, _, hqB⟩ := Finset.mem_biUnion.mp hq
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hqB).1, Finset.mem_univ _⟩
    · intro hq
      have hpq := (Finset.mem_erase.mp hq).1
      obtain ⟨B, hB, hp, hq⟩ := cover p q hpq.symm
      exact Finset.mem_biUnion.mpr ⟨B, throughPoint_mem.mpr ⟨hB, hp⟩, Finset.mem_erase.mpr ⟨hpq, hq⟩⟩
  have hdisjoint : (↑T : Set (Finset (Fin 13))).PairwiseDisjoint (fun B => B.erase p) := by
    intro B hB D hD hBD
    refine Finset.disjoint_left.mpr fun q hqB hqD => hBD ?_
    obtain ⟨hB', hpB⟩ := throughPoint_mem.mp hB
    obtain ⟨hD', hpD⟩ := throughPoint_mem.mp hD
    obtain ⟨hqp, hqB'⟩ := Finset.mem_erase.mp hqB
    have hqD' := (Finset.mem_erase.mp hqD).2
    exact planeQuartet_unique_through_pair round closed hB' hD' hqp.symm hpB hqB' hpD hqD'
  have hcard : ∑ B ∈ T, (B.erase p).card = 12 := by
    rw [← Finset.card_biUnion hdisjoint, hunion, Finset.card_erase_of_mem (Finset.mem_univ p)]
    simp
  have hsize : (∑ B ∈ T, (B.erase p).card) = T.card * 3 := by
    calc
      _ = ∑ _B ∈ T, (3 : ℕ) := by
        apply Finset.sum_congr rfl
        intro B hB
        obtain ⟨hB', hpB⟩ := throughPoint_mem.mp hB
        rw [Finset.card_erase_of_mem hpB, hB'.1]
      _ = _ := by simp
  change T.card = 4
  omega

include round closed cover in
theorem planeQuartets_card : (planeQuartets h system).card = 13 := by
  let T := planeQuartets h system
  have hpoint : (∑ p : Fin 13, (planeQuartetsThrough h system p).card) = 52 := by
    simp [planeQuartets_through_point_card round closed cover]
  have hdouble : (∑ p : Fin 13, (planeQuartetsThrough h system p).card) = ∑ B ∈ T, B.card := by
    change (∑ p : Fin 13, (T.filter (fun B => p ∈ B)).card) = ∑ B ∈ T, B.card
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [← Finset.sum_filter]
    simp
  have hsize : (∑ B ∈ T, B.card) = T.card * 4 := by
    calc
      _ = ∑ _B ∈ T, (4 : ℕ) := by
        apply Finset.sum_congr rfl
        intro B hB
        exact ((Finset.mem_filter.mp hB).2).1
      _ = _ := by simp
  change T.card = 13
  omega

include round closed cover in
/-- Distinct quartets in a quartet-covered thirteen-plane system meet at exactly one plane. -/
theorem planeQuartets_existsUnique_intersection {B D : Finset (Fin 13)}
    (hB : IsPlaneQuartet h system B) (hD : IsPlaneQuartet h system D) (hBD : B ≠ D) :
    ∃! p, p ∈ B ∧ p ∈ D := by
  suffices exists_point : ∃ p, p ∈ B ∧ p ∈ D by
    obtain ⟨p, hpB, hpD⟩ := exists_point
    refine ⟨p, ⟨hpB, hpD⟩, fun q hq => ?_⟩
    by_contra hqp
    exact hBD (planeQuartet_unique_through_pair round closed hB hD hqp hq.1 hpB hq.2 hpD)
  by_contra hex
  obtain ⟨p, hpB⟩ := Finset.card_pos.mp (show 0 < B.card by rw [hB.1]; decide)
  have hpD : p ∉ D := fun hp => hex ⟨p, hpB, hp⟩
  let line (q : Fin 13) : Finset (Fin 13) := if hpq : p ≠ q then (cover p q hpq).choose else B
  have line_spec (q : Fin 13) (hq : q ∈ D) :
      IsPlaneQuartet h system (line q) ∧ p ∈ line q ∧ q ∈ line q := by
    have hpq : p ≠ q := fun he => hpD (he ▸ hq)
    simpa only [line, dite_eq_left hpq] using (cover p q hpq).choose_spec
  have hto : Set.MapsTo line ↑D ↑((planeQuartetsThrough h system p).erase B) := by
    intro q hq
    obtain ⟨hC, hpC, hqC⟩ := line_spec q hq
    have hn : line q ≠ B := fun he => hex ⟨q, he ▸ hqC, hq⟩
    exact Finset.mem_erase.mpr ⟨hn, throughPoint_mem.mpr ⟨hC, hpC⟩⟩
  have hinj : Set.InjOn line ↑D := by
    intro q hq r hr he
    by_contra hqr
    obtain ⟨hC, hpC, hqC⟩ := line_spec q hq
    have hrC : r ∈ line q := he ▸ (line_spec r hr).2.2
    have he' := planeQuartet_unique_through_pair round closed hC hD hqr hqC hrC hq hr
    exact hpD (he' ▸ hpC)
  have hc := Finset.card_le_card_of_injOn line hto hinj
  rw [hD.1, Finset.card_erase_of_mem (throughPoint_mem.mpr ⟨hB, hpB⟩),
    planeQuartets_through_point_card round closed cover] at hc
  omega

include round closed cover in
/-- The incidence consequences of quartet coverage in the thirteen-plane support and incidence theorem (ii). -/
theorem thirteenPlane_quartet_incidence :
    (∀ i j : Fin 13, i ≠ j → ∃! B, IsPlaneQuartet h system B ∧ i ∈ B ∧ j ∈ B) ∧
    (planeQuartets h system).card = 13 ∧
    (∀ p, (planeQuartetsThrough h system p).card = 4) ∧
    (∀ B D : Finset (Fin 13), IsPlaneQuartet h system B → IsPlaneQuartet h system D → B ≠ D →
      ∃! p, p ∈ B ∧ p ∈ D) := by
  refine ⟨?_, planeQuartets_card round closed cover, planeQuartets_through_point_card round closed cover,
    fun _ _ => planeQuartets_existsUnique_intersection round closed cover⟩
  intro i j hij
  obtain ⟨B, hB, hiB, hjB⟩ := cover i j hij
  exact ⟨B, ⟨hB, hiB, hjB⟩, fun D hD =>
    planeQuartet_unique_through_pair round closed hD.1 hB hij hD.2.1 hD.2.2 hiB hjB⟩

end
end ThirteenPlanes.RoundCubics
