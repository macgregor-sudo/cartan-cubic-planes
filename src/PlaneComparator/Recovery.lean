/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PlaneComparator.Core
public import ThirteenPlanes.Shares.RecoveryProducts
public import ThirteenPlanes.Shares.RecoveryEndpoints
public import ThirteenPlanes.Shares.RecoveryUnlabelled
public import ThirteenPlanes.Shares.Support

@[expose] public section

/-! The projection sum rule and recovery conclusions on the challenge's intrinsic pencil. -/

open scoped BigOperators RealInnerProductSpace

namespace Challenge

open ThirteenPlanes ThirteenPlanes.RoundCubics Bridge

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem sum_rule {m : ℕ} (_hm : 3 ≤ m) (d : Cubic V) (c : ℝ) (U : Fin m → Submodule ℝ V)
    (hd : Eikonal d c) (hU : Planes d U) :
    (∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      share d U i j k ∈ Set.Icc 0 1 ∧
      (share d U i j k = 1 ↔ U k ≤ mixedSpace d (U i) (U j)) ∧
      (share d U i j k = 0 ↔ (U k).IsOrtho (mixedSpace d (U i) (U j)))) ∧
    (∀ i j, i ≠ j → (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), share d U i j k) = 2) ∧
    (∑ t : IncreasingTriple m, share d U t.1.1 t.1.2.1 t.1.2.2) = (m : ℝ) * ((m : ℝ) - 1) / 3 := by
  let P := planeDecomp hU
  have round := (eikonal_iff d c).mp hd
  have closed := planeDecomp_closed hU
  obtain ⟨hb, hp, ht⟩ := planeShare_sum_rule round closed
  refine ⟨?_, ?_, ?_⟩
  · intro i j k hij hki hkj
    have heq (a : Fin m) : (planeDecomp hU).plane a = U a := rfl
    simpa only [share_eq hU, mixed_space_eq, heq] using hb i j k hij hki hkj
  · intro i j hij
    calc
      _ = ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
          planeShare (toSymmetric d) P i j k :=
        Finset.sum_congr rfl (fun k _ => (share_eq hU i j k).symm)
      _ = 2 := hp i j hij
  · calc
      _ = ∑ t : IncreasingTriple m, planeShare (toSymmetric d) P t.1.1 t.1.2.1 t.1.2.2 :=
        Finset.sum_congr rfl (fun t _ => (share_eq hU t.1.1 t.1.2.1 t.1.2.2).symm)
      _ = _ := ht

open Classical in
/-- At least 52 unordered triples have positive share in a closed thirteen-plane system.
If exactly 52 are positive, each unordered triple has share zero or one. -/
theorem thirteen_plane_share_support (d : Cubic V) (c : ℝ) (U : Fin 13 → Submodule ℝ V)
    (hd : Eikonal d c) (hU : Planes d U) :
    let support := Finset.univ.filter (fun t : IncreasingTriple 13 =>
      0 < share d U t.val.1 t.val.2.1 t.val.2.2)
    52 ≤ support.card ∧ (support.card = 52 → ∀ t : IncreasingTriple 13,
      share d U t.val.1 t.val.2.1 t.val.2.2 = 0 ∨
      share d U t.val.1 t.val.2.1 t.val.2.2 = 1) := by
  have round := (eikonal_iff d c).mp hd
  have closed := planeDecomp_closed hU
  have support_eq : positivePlaneTriples (toSymmetric d) (planeDecomp hU) =
      Finset.univ.filter (fun t : IncreasingTriple 13 =>
        0 < share d U t.val.1 t.val.2.1 t.val.2.2) := by
    ext t
    simp only [positivePlaneTriples, unorderedPlaneShare, Finset.mem_filter, share_eq hU]
  dsimp only
  rw [← support_eq]
  refine ⟨(thirteenPlane_share_counts round closed).2.2, ?_⟩
  intro count t
  obtain ⟨hij, hjk⟩ := t.property
  have binary := (thirteenPlane_positive_eq_fifty_two_iff round closed).mp count
  simpa only [share_eq hU] using
    binary t.val.1 t.val.2.1 t.val.2.2 hij.ne (hij.trans hjk).ne' hjk.ne'

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem energy_recovery_labeled (d e : Cubic V) (c t s : ℝ) (U : ι → Submodule ℝ V)
    (hd : Eikonal d c) (he : Eikonal e c) (hU : Planes d U) (hU' : Planes e U)
    (hm : 1 < Fintype.card ι)
    (h : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x ∈ (U i ⊔ U j) ⊔ U k,
      pencilEnergy d U c t x = pencilEnergy e U c s x) :
    t = s ∧ (t ≠ 0 → t ≠ 1 → ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ x, e.eval x = ε * d.eval x ∧ pencil e U s x = ε * pencil d U t x) := by
  have hsame : planeDecomp hU' = planeDecomp hU := rfl
  have hclosed : IsClosedPlaneSystem (toSymmetric e) (planeDecomp hU) :=
    hsame ▸ planeDecomp_closed hU'
  have henergy : EqualPlaneTripleEnergies (toSymmetric d) (toSymmetric e) (planeDecomp hU) c t s := by
    intro i j k hij hik hjk x hx
    rw [pencil_energy_eq hU, ← hsame, pencil_energy_eq hU']
    exact h i j k hij hik hjk x hx
  obtain ⟨hparam, hsign⟩ := planePencil_labeled_recovery
    ((eikonal_iff d c).mp hd) ((eikonal_iff e c).mp he)
    (planeDecomp_closed hU) hclosed hm henergy
  refine ⟨hparam, fun h0 h1 => ?_⟩
  rcases hsign h0 h1 with ⟨heq, hp⟩ | ⟨heq, hp⟩
  · rw [← hsame] at hp
    refine ⟨1, Or.inl rfl, fun x => ⟨?_, ?_⟩⟩
    · rw [← eval_toSymmetric e, ← eval_toSymmetric d, heq, one_mul]
    · rw [pencil_eq_of_cubic_eq hU hU' hp, one_mul]
  · rw [← hsame] at hp
    refine ⟨-1, Or.inr rfl, fun x => ⟨?_, ?_⟩⟩
    · rw [← eval_toSymmetric e, ← eval_toSymmetric d, heq, eval_neg, neg_one_mul]
    · rw [pencil_eq_neg_of_cubic_eq hU hU' hp, neg_one_mul]

theorem energy_recovery_endpoints (d : Cubic V) (c t : ℝ) (U : ι → Submodule ℝ V)
    (hd : Eikonal d c) (hU : Planes d U) (hm : 1 < Fintype.card ι) (ht : t = 0 ∨ t = 1) :
    ∃ e : Cubic V, Eikonal e c ∧ Planes e U ∧
      (∀ x, pencilEnergy e U c t x = pencilEnergy d U c t x) ∧
      pencil e U t ≠ pencil d U t ∧ pencil e U t ≠ fun x => -pencil d U t x := by
  obtain ⟨g, hg, hc, henergy, hne, hnneg⟩ := planePencil_endpoint_nonunique
    ((eikonal_iff d c).mp hd) (planeDecomp_closed hU) hm t ht
  let e := fromSymmetric g
  have he : toSymmetric e = g := toSymmetric_fromSymmetric g
  have hU' : Planes e U := ⟨hU.1, fun i => ⟨(hU.2 i).1, hc i⟩⟩
  have hsame : planeDecomp hU' = planeDecomp hU := rfl
  refine ⟨e, (eikonal_iff e c).mpr (he ▸ hg), hU', ?_, ?_, ?_⟩
  · intro x
    rw [← pencil_energy_eq hU', ← pencil_energy_eq hU, he, hsame]
    exact henergy x
  · intro heq
    apply hne
    apply Peirce.cubic_eq_of_diagonal_eq
    intro x
    rw [pencil_eval_eq hU, ← he, ← hsame, pencil_eval_eq hU']
    exact congrFun heq x
  · intro heq
    apply hnneg
    apply Peirce.cubic_eq_of_diagonal_eq
    intro x
    rw [eval_neg, pencil_eval_eq hU, ← he, ← hsame, pencil_eval_eq hU']
    exact congrFun heq x

theorem energy_recovery_unlabelled (d e : Cubic V) (c t s : ℝ)
    (U : ι → Submodule ℝ V) (W : κ → Submodule ℝ V)
    (hd : Eikonal d c) (he : Eikonal e c) (hU : Planes d U) (hW : Planes e W)
    (hm : 1 < Fintype.card ι) (hn : 1 < Fintype.card κ)
    (ht : 0 < t) (hs : 0 < s) (ht' : t ≠ 1) (hs' : s ≠ 1)
    (h : ∀ x, pencilEnergy d U c t x = pencilEnergy e W c s x) :
    ∃ f : ι ≃ κ, (∀ i, U i = W (f i)) ∧ t = s ∧
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x, pencil e W s x = ε * pencil d U t x := by
  have henergy (x : V) :
      normalizedPencilEnergy (toSymmetric d) (planeDecomp hU) c t x =
      normalizedPencilEnergy (toSymmetric e) (planeDecomp hW) c s x := by
    rw [pencil_energy_eq hU, pencil_energy_eq hW]
    exact h x
  obtain ⟨f, hf, hparam, hsign⟩ := planePencil_unlabelled_recovery
    (planeDecomp hU) (planeDecomp hW) ((eikonal_iff d c).mp hd) ((eikonal_iff e c).mp he)
    (planeDecomp_closed hU) (planeDecomp_closed hW) hm hn ht hs ht' hs' henergy
  refine ⟨f, hf, hparam, ?_⟩
  rcases hsign with ⟨_, hp⟩ | ⟨_, hp⟩
  · exact ⟨1, Or.inl rfl, fun x => by rw [pencil_eq_of_cubic_eq hU hW hp, one_mul]⟩
  · exact ⟨-1, Or.inr rfl, fun x => by rw [pencil_eq_neg_of_cubic_eq hU hW hp, neg_one_mul]⟩

end

end Challenge
