module

public import ThirteenPlanes.AlbertGrading.Recognition.ExteriorStep

@[expose] public section

/-!
# The core of the recognition of systems with 52 positive shares in `J_T`

A system of thirteen frames of `J_T` with every pair in a quartet (`TitsSystem`) is carried by a
trace-preserving automorphism onto the graded system, frame by frame as sets, with the frames
matched bijectively to the thirteen points.

Pair normalization moves two frames of a quartet to the eigenframes of `ι₀(Z)` and `ι₀(X)`. The other two lie in their product space and are the eigenframes of `ι₀(XZ)`
and `ι₀(XZ²)` by `graded_of_planes`. An exterior frame is unbiased to the four eigenframes,
hence orthogonal to `Q₀⁰` by `exterior_orthogonal`. The exterior frame normal form moves it
to `(1, ω^a, ω^{-a})/3` by an automorphism fixing `Q₀`. For each eigenframe, the two other
frames of its quartet with the exterior frame lie in their product space. Applying
`graded_of_planes` again identifies the remaining graded frames.




-/

open scoped Matrix BigOperators RealInnerProductSpace
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-- Representatives of the thirteen points `{±g}` of `PG(2,3)`. -/
def pointRep : Fin 13 → Charge :=
  ![chargeFrom (0, 1) 0, chargeFrom (1, 0) 0, chargeFrom (1, 1) 0, chargeFrom (2, 1) 0,
    chargeFrom 0 2, chargeFrom (0, 1) 2, chargeFrom (0, 1) 1, chargeFrom (1, 0) 2,
    chargeFrom (1, 0) 1, chargeFrom (1, 1) 2, chargeFrom (1, 1) 1, chargeFrom (2, 1) 2,
    chargeFrom (2, 1) 1]

theorem pointRep_ne_zero (m : Fin 13) : pointRep m ≠ 0 := by
  fin_cases m <;> decide

theorem pointRep_distinct (m n : Fin 13) (hmn : m ≠ n) :
    pointRep n ≠ pointRep m ∧ pointRep n ≠ -pointRep m := by
  fin_cases m <;> fin_cases n <;> first | exact absurd rfl hmn | decide

theorem pointRep_injective_range {m n : Fin 13}
    (h : Set.range (gradedFrame (pointRep m)) = Set.range (gradedFrame (pointRep n))) : m = n := by
  by_contra hmn
  rcases gradedRange_eq_imp (pointRep_ne_zero m) h with e | e
  · exact (pointRep_distinct m n hmn).1 e
  · exact (pointRep_distinct m n hmn).2 e

theorem two_others {B : Finset (Fin 13)} (hB : B.card = 4) {i j : Fin 13} (hi : i ∈ B) (hj : j ∈ B)
    (hij : i ≠ j) : ∃ t t', t ∈ B ∧ t' ∈ B ∧ t ≠ t' ∧ t ≠ i ∧ t ≠ j ∧ t' ≠ i ∧ t' ≠ j := by
  have hc : ((B.erase i).erase j).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩),
      Finset.card_erase_of_mem hi, hB]
  obtain ⟨t, t', htt, he⟩ := Finset.card_eq_two.mp hc
  have ht : t ∈ (B.erase i).erase j := by rw [he]; simp
  have ht' : t' ∈ (B.erase i).erase j := by rw [he]; simp
  simp only [Finset.mem_erase] at ht ht'
  exact ⟨t, t', ht.2.2, ht'.2.2, htt, ht.2.1, ht.1, ht'.2.1, ht'.1⟩

theorem exists_not_mem {B : Finset (Fin 13)} (hB : B.card = 4) : ∃ H, H ∉ B := by
  by_contra h
  push_neg at h
  have : B = Finset.univ := Finset.eq_univ_of_forall h
  rw [this, Finset.card_univ, Fintype.card_fin] at hB
  norm_num at hB

theorem pair_attained {P : Fin 13 → ZMod 3 → CompactTits} (hS : TitsSystem P) {t t' : Fin 13}
    (htt : t ≠ t') {A A' : Set CompactTits}
    (ht : Set.range (P t) = A ∨ Set.range (P t) = A')
    (ht' : Set.range (P t') = A ∨ Set.range (P t') = A') :
    (∃ s, Set.range (P s) = A) ∧ (∃ s, Set.range (P s) = A') := by
  have hne := hS.range_ne htt
  rcases ht with h1 | h1 <;> rcases ht' with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact ⟨⟨t, h1⟩, ⟨t', h2⟩⟩
  · exact ⟨⟨t', h2⟩, ⟨t, h1⟩⟩
  · exact absurd (h1.trans h2.symm) hne

/-- The two other frames of the quartet through two graded frames are graded. -/
theorem quartet_step {P : Fin 13 → ZMod 3 → CompactTits} (hS : TitsSystem P) {i j : Fin 13}
    (hij : i ≠ j) {g h : Charge} (hd : ¬ F3Dependent g h)
    (hi : Set.range (P i) = Set.range (gradedFrame g))
    (hj : Set.range (P j) = Set.range (gradedFrame h)) :
    (∃ s, Set.range (P s) = Set.range (gradedFrame (g + h))) ∧
      (∃ s, Set.range (P s) = Set.range (gradedFrame (g + -h))) := by
  obtain ⟨B, hB, hiB, hjB, hle⟩ := hS.quartet i j hij
  obtain ⟨t, t', ht, ht', htt, hti, htj, hti', htj'⟩ := two_others hB hiB hjB hij
  have hplane : ∀ s ∈ B, s ≠ i → s ≠ j → titsFramePlane (P s) ≤
      titsProdSpace (titsFramePlane (gradedFrame g)) (titsFramePlane (gradedFrame h)) := by
    intro s hs hsi hsj
    rw [← titsFramePlane_congr hi, ← titsFramePlane_congr hj]
    exact hle s hs hsi hsj
  exact pair_attained hS htt (graded_of_planes (hS.frame t) hd (hplane t ht hti htj))
    (graded_of_planes (hS.frame t') hd (hplane t' ht' hti' htj'))

theorem visible_classes (v : WeylLabel) (hv : v ≠ 0) :
    ∃ m : Fin 13, (m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) ∧
      (chargeFrom v 0 = pointRep m ∨ chargeFrom v 0 = -pointRep m) := by
  obtain ⟨a, b⟩ := v
  fin_cases a <;> fin_cases b <;> first
    | exact absurd rfl hv
    | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩ | exact ⟨3, by decide⟩

end

end ThirteenPlanes.AlbertGrading
