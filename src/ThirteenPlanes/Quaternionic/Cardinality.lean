module

public import ThirteenPlanes.Quaternionic.FrameGeometry
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fin.Embedding
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Finite selection for quaternionic bases.

A finite obstruction to six pairwise unbiased native bases gives the corresponding cardinality
bound for arbitrary sets of bases. -/

noncomputable section

namespace QuaternionicMUB

lemma Frame.MutuallyUnbiased.symm {F G : Frame}
    (h : F.MutuallyUnbiased G) : G.MutuallyUnbiased F := by
  intro a b
  rw [traceForm_comm]
  exact h b a

lemma QBasis.MutuallyUnbiased.symm {U V : QBasis}
    (h : U.MutuallyUnbiased V) : V.MutuallyUnbiased U := by
  apply (V.mutuallyUnbiased_iff_toFrame U).mpr
  exact ((U.mutuallyUnbiased_iff_toFrame V).mp h).symm

lemma IsMUBFamily.comp_embedding {ι κ : Type*} {B : ι → QBasis}
    (hB : IsMUBFamily B) (e : κ ↪ ι) : IsMUBFamily (fun k => B (e k)) := by
  intro i j hij
  exact hB (fun h => hij (e.injective h))

/-- Extract six distinct indices from any finite family larger than five. -/
theorem card_le_five_of_no_six
    (hno : ∀ B : Fin 6 → QBasis, ¬ IsMUBFamily B)
    {ι : Type*} [Fintype ι] (B : ι → QBasis) (hB : IsMUBFamily B) :
    Fintype.card ι ≤ 5 := by
  by_contra hn
  have hcard : Fintype.card (Fin 6) ≤ Fintype.card ι := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact hno (fun k => B (e k)) (hB.comp_embedding e)

/-- Infinite native basis sets also contain six distinct members, so the set
endpoint proves finiteness as well as the numerical ncard bound. -/
theorem set_finite_card_le_five_of_no_six
    (hno : ∀ B : Fin 6 → QBasis, ¬ IsMUBFamily B)
    (S : Set QBasis) (hS : S.Pairwise QBasis.MutuallyUnbiased) :
    S.Finite ∧ S.ncard ≤ 5 := by
  have hfinite : S.Finite := by
    by_contra hinfinite
    let e : Fin 6 ↪ S := Fin.valEmbedding.trans (Set.Infinite.natEmbedding S hinfinite)
    apply hno (fun i => (e i).val)
    intro i j hij
    exact hS (e i).property (e j).property
      (fun heq => hij (e.injective (Subtype.ext heq)))
  refine ⟨hfinite, ?_⟩
  letI := hfinite.fintype
  have hB : IsMUBFamily (fun x : S => x.val) := by
    intro i j hij
    exact hS i.property j.property (fun heq => hij (Subtype.ext heq))
  simpa only [Set.fintypeCard_eq_ncard] using
    card_le_five_of_no_six hno (fun x : S => x.val) hB

/-- Completion of every hypothetical six-tuple, together with no seven,
eliminates six without treating completion as an axiom. -/
theorem no_six_of_extension_and_no_seven
    (hext : ∀ B : Fin 6 → QBasis, IsMUBFamily B →
      ∃ U : QBasis, ∀ i, (B i).MutuallyUnbiased U)
    (hseven : ∀ B : Fin 7 → QBasis, ¬ IsMUBFamily B) :
    ∀ B : Fin 6 → QBasis, ¬ IsMUBFamily B := by
  intro B hB
  obtain ⟨U, hU⟩ := hext B hB
  let C : Fin 7 → QBasis := Fin.cons U B
  apply hseven C
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · intro j
    refine Fin.cases ?_ (fun b => ?_) j
    · intro hij
      exact (hij rfl).elim
    · intro _
      simpa [C] using (hU b).symm
  · intro j
    refine Fin.cases ?_ (fun b => ?_) j
    · intro _
      simpa [C] using hU a
    · intro hab
      have hab' : a ≠ b := fun h => hab (congrArg Fin.succ h)
      simpa [C] using hB hab'

end QuaternionicMUB
