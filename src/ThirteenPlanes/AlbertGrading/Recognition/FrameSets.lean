/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.AlbertGrading.Recognition.NonVacuity

@[expose] public section

/-! Recognition for a set of thirteen distinct unordered frames. -/

open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

open Tits

/-- After indexing the thirteen distinct frames, their unordered outcomes agree with the whole
graded system up to one permutation of its thirteen projective points. -/
theorem recognition_entire_graded_system (F : Fin 13 → ZMod 3 → CompactTits)
    (distinct : Function.Injective (fun i => Set.range (F i)))
    (frames : ∀ i, IsTitsFrame (F i))
    (eigenframes : ∀ v : WeylLabel, v ≠ 0 → ∃ i, Set.range (F i) = Set.range (weylEigenframe v))
    (exterior : ∃ i, Set.range (F i) = Set.range exteriorPoint)
    (closure : ∀ i j, Set.range (F i) ≠ Set.range (F j) →
      ∀ x ∈ ({titsContrast (F i), compactInvolution (titsContrast (F i))} : Set (FirstTits ℂ)),
      ∀ y ∈ ({titsContrast (F j), compactInvolution (titsContrast (F j))} : Set (FirstTits ℂ)),
      ∃ c : ℂ, c ≠ 0 ∧ ∃ m ∈ titsContrastLines F, firstTitsJordanProduct x y = c • m) :
    ∃ σ : Equiv.Perm (Fin 13), ∀ i, Set.range (F i) = Set.range (gradedFrame (pointRep (σ i))) := by
  classical
  have recognized := recognition F frames eigenframes exterior closure
  have represented (i : Fin 13) : ∃ m : Fin 13, Set.range (F i) = Set.range (gradedFrame (pointRep m)) := by
    obtain ⟨g, hg, hr⟩ := recognized i
    obtain ⟨m, eq | eq⟩ := charge_point_cover g hg
    · exact ⟨m, eq ▸ hr⟩
    · exact ⟨m, by simpa only [eq, range_gradedFrame_neg] using hr⟩
  choose f hf using represented
  have inj : Function.Injective f := by
    intro i j eq
    apply distinct
    simp only [hf i, hf j, eq]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj), hf⟩

end ThirteenPlanes.AlbertGrading
