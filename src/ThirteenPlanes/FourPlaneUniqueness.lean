module

public import ThirteenPlanes.Shares.PairCompletions

@[expose] public section

/-! An orthogonal pair of planes has at most one completion to a four-plane system. -/

namespace ThirteenPlanes.RoundCubics

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : SymmetricCubic V} {c : ℝ}

/-- A closed piece in the sum of two orthogonal closed pieces lies in one summand. -/
theorem closedPiece_le_one_of_le_sup {C D S : Submodule ℝ V}
    (round : IsRound h c) (orth : C.IsOrtho D)
    (cC : IsClosedPiece h C) (cD : IsClosedPiece h D) (cS : IsClosedPiece h S)
    (contained : S ≤ C ⊔ D) : S ≤ C ∨ S ≤ D := by
  have covered (x : V) (hx : x ∈ S) : x ∈ C ∨ x ∈ D := by
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (contained hx)
    obtain ⟨perp, mixed⟩ := (mixedProductLaw round orth cC cD).1 hu hv
    have hu' : h.L u u ∈ C ⊔ D := (le_sup_left : C ≤ C ⊔ D) (cC hu hu)
    have hv' : h.L v v ∈ C ⊔ D := (le_sup_right : D ≤ C ⊔ D) (cD hv hv)
    have him := (C ⊔ D).sub_mem ((C ⊔ D).sub_mem (contained (cS hx hx)) hu') hv'
    have htwice : h.L (u + v) (u + v) - h.L u u - h.L v v = (2 : ℝ) • h.L u v := by
      simp only [map_add, LinearMap.add_apply, h.L_comm v u]
      module
    rw [htwice] at him
    have hp : h.L u v ∈ C ⊔ D := ((C ⊔ D).smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp him
    have hz := (inner_self_eq_zero (𝕜 := ℝ)).mp (Submodule.inner_right_of_mem_orthogonal hp perp)
    by_cases huv : u = 0
    · exact Or.inr (by simpa [huv] using hv)
    · have hnv : v = 0 := by
        by_contra hvn
        have hn := mul_pos (mul_pos round.positive (pow_pos (norm_pos_iff.mpr huv) 2))
          (pow_pos (norm_pos_iff.mpr hvn) 2)
        rw [hz, norm_zero] at mixed
        linarith
      exact Or.inl (by simpa [hnv] using hu)
  by_cases all : S ≤ C
  · exact Or.inl all
  · obtain ⟨x, hx, hnC⟩ := IsConcreteLE.not_le_iff_exists.mp all
    have hxD := (covered x hx).resolve_left hnC
    refine Or.inr fun y hy => ?_
    by_contra hnD
    have hyC := (covered y hy).resolve_right hnD
    rcases covered (x+y) (S.add_mem hx hy) with hs | hs
    · exact hnC ((C.add_mem_iff_left hyC).mp hs)
    · exact hnD ((D.add_mem_iff_right hxD).mp hs)

/-- Two complete systems of four closed planes agreeing on an ordered pair differ
only by a permutation fixing that pair. -/
theorem fourPlane_completion_unique (round : IsRound h c)
    {P Q : PlaneDecomposition V (Fin 4)} (cP : IsClosedPlaneSystem h P)
    (cQ : IsClosedPlaneSystem h Q) (first : P.plane 0 = Q.plane 0) (second : P.plane 1 = Q.plane 1) :
    ∃ e : Equiv.Perm (Fin 4), e 0 = 0 ∧ e 1 = 1 ∧ ∀ i, P.plane i = Q.plane (e i) := by
  have other (R : PlaneDecomposition V (Fin 4)) (cR : IsClosedPlaneSystem h R) :
      mixedProductSpace h (R.plane 0) (R.plane 1) = R.plane 2 ⊔ R.plane 3 :=
    (fourPlane_unit_shares round cR (i := 0) (j := 1) (k := 2) (l := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2.2
  have hs : P.plane 2 ⊔ P.plane 3 = Q.plane 2 ⊔ Q.plane 3 := by
    rw [← other P cP, ← other Q cQ, first, second]
  have sides (i : Fin 4) (inc : P.plane i ≤ P.plane 2 ⊔ P.plane 3) :
      P.plane i = Q.plane 2 ∨ P.plane i = Q.plane 3 := by
    rw [hs] at inc
    rcases closedPiece_le_one_of_le_sup round (Q.pairwise_orthogonal (by decide : (2 : Fin 4) ≠ 3))
      (cQ 2) (cQ 3) (cP i) inc with hl | hr
    · exact Or.inl (Submodule.eq_of_le_of_finrank_le hl (by rw [P.dimension, Q.dimension]))
    · exact Or.inr (Submodule.eq_of_le_of_finrank_le hr (by rw [P.dimension, Q.dimension]))
  have distinct : P.plane 2 ≠ P.plane 3 := by
    intro he
    have hd := (P.pairwise_orthogonal (by decide : (2 : Fin 4) ≠ 3)).disjoint.eq_bot
    rw [← he, inf_idem] at hd
    have hm := P.dimension 2
    rw [hd, finrank_bot] at hm
    omega
  rcases sides 2 le_sup_left with h2 | h2 <;> rcases sides 3 le_sup_right with h3 | h3
  · exact (distinct (h2.trans h3.symm)).elim
  · exact ⟨Equiv.refl _, rfl, rfl, fun i => by fin_cases i <;> assumption⟩
  · refine ⟨Equiv.swap 2 3, by decide, by decide, fun i => ?_⟩
    fin_cases i <;> simp [Equiv.swap_apply_def] <;> assumption
  · exact (distinct (h2.trans h3.symm)).elim

end ThirteenPlanes.RoundCubics
