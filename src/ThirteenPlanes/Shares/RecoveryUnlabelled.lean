module

public import ThirteenPlanes.Shares.RecoveryProducts
public import ThirteenPlanes.Shares.PlaneTransport
public import ThirteenPlanes.PlaneEnergyExtrema

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {h g : SymmetricCubic V} {c t s : ℝ}

private theorem nonzero_point_in_plane (S : Submodule ℝ V) (dimension : Module.finrank ℝ S = 2) :
    ∃ x : V, x ∈ S ∧ x ≠ 0 := by
  let e := (stdOrthonormalBasis ℝ S).reindex (finCongr dimension)
  have hnorm : ‖(e 0 : V)‖ = 1 := e.orthonormal.norm_eq_one 0
  exact ⟨e 0, (e 0).property, norm_pos_iff.mp (by rw [hnorm]; norm_num)⟩

omit [Fintype ι] in
private theorem plane_index_injective (P : PlaneDecomposition V ι) : Function.Injective P.plane := by
  intro i j he
  by_contra hn
  obtain ⟨x, hx, hnz⟩ := nonzero_point_in_plane (P.plane i) (P.dimension i)
  have hz := (P.pairwise_orthogonal hn).inner_eq hx (he ▸ hx)
  exact hnz ((inner_self_eq_zero (𝕜 := ℝ)).mp hz)

omit [Fintype ι] in
private theorem plane_eq_of_covered_by_planes (P : PlaneDecomposition V ι)
    (S : Submodule ℝ V) (dimension : Module.finrank ℝ S = 2)
    (cover : ∀ x ∈ S, ∃ i, x ∈ P.plane i) : ∃ i, S = P.plane i := by
  obtain ⟨a, ha, hna⟩ := nonzero_point_in_plane S dimension
  obtain ⟨i, hi⟩ := cover a ha
  refine ⟨i, Submodule.eq_of_le_of_finrank_le ?_ (by rw [dimension, P.dimension])⟩
  intro x hx
  obtain ⟨j, hj⟩ := cover x hx
  by_cases hij : i = j
  · exact hij ▸ hj
  obtain ⟨k, hk⟩ := cover (a + x) (S.add_mem ha hx)
  by_cases hik : i = k
  · exact (P.plane i).sub_mem (hik ▸ hk) hi |> fun h => by simpa using h
  · have h₁ := (P.pairwise_orthogonal hik).inner_eq hi hk
    have h₂ := (P.pairwise_orthogonal hij).inner_eq hi hj
    rw [inner_add_right, h₂, add_zero] at h₁
    exact (hna ((inner_self_eq_zero (𝕜 := ℝ)).mp h₁)).elim

omit [Fintype ι] [Fintype κ] in
private theorem plane_cover_from_unit_levels (P : PlaneDecomposition V ι) (Q : PlaneDecomposition V κ)
    (level : ∀ x : V, ‖x‖ = 1 → ((∃ i, x ∈ P.plane i) ↔ ∃ j, x ∈ Q.plane j)) :
    ∀ i : ι, ∃ j : κ, P.plane i = Q.plane j := by
  intro i
  apply plane_eq_of_covered_by_planes Q (P.plane i) (P.dimension i)
  intro x hx
  by_cases hz : x = 0
  · obtain ⟨a, ha, hna⟩ := nonzero_point_in_plane (P.plane i) (P.dimension i)
    let u := ‖a‖⁻¹ • a
    have hu : ‖u‖ = 1 := by
      rw [show u = ‖a‖⁻¹ • a from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hna)]
    obtain ⟨j, _⟩ := (level u hu).mp ⟨i, (P.plane i).smul_mem _ ha⟩
    exact ⟨j, hz ▸ (Q.plane j).zero_mem⟩
  · let u := ‖x‖⁻¹ • x
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hu : ‖u‖ = 1 := by
      rw [show u = ‖x‖⁻¹ • x from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hn]
    obtain ⟨j, hj⟩ := (level u hu).mp ⟨i, (P.plane i).smul_mem _ hx⟩
    refine ⟨j, ?_⟩
    have hu' := (Q.plane j).smul_mem ‖x‖ hj
    rw [show u = ‖x‖⁻¹ • x from rfl, smul_smul, mul_inv_cancel₀ hn, one_smul] at hu'
    exact hu'

/-- The full unlabelled assertion of the energy recovery theorem (iii), for independently indexed
complete systems and their actual normalized pencil energy. -/
theorem planePencil_unlabelled_recovery (P : PlaneDecomposition V ι) (Q : PlaneDecomposition V κ)
    (rh : IsRound h c) (rg : IsRound g c)
    (ch : IsClosedPlaneSystem h P) (cg : IsClosedPlaneSystem g Q)
    (m : 1 < Fintype.card ι) (n : 1 < Fintype.card κ)
    (ht : 0 < t) (hs : 0 < s) (ht₁ : t ≠ 1) (hs₁ : s ≠ 1)
    (eq : ∀ x : V, normalizedPencilEnergy h P c t x = normalizedPencilEnergy g Q c s x) :
    ∃ e : ι ≃ κ, (∀ i, P.plane i = Q.plane (e i)) ∧ t = s ∧
      ((g = h ∧ interactionCubic (planePencil g Q) s = interactionCubic (planePencil h P) t) ∨
      (g = -h ∧ interactionCubic (planePencil g Q) s = -interactionCubic (planePencil h P) t)) := by
  have levels (x : V) (hx : ‖x‖ = 1) :
      (∃ i, x ∈ P.plane i) ↔ ∃ j, x ∈ Q.plane j := by
    simpa only [Set.mem_iUnion, SetLike.mem_coe] using
      (((planePencilExtrema rh ch m ht.le ht₁).1 x hx).2.symm.trans
        ((by rw [eq x]) : normalizedPencilEnergy h P c t x = 1 ↔ normalizedPencilEnergy g Q c s x = 1)).trans
          ((planePencilExtrema rg cg n hs.le hs₁).1 x hx).2
  choose f hf using plane_cover_from_unit_levels P Q levels
  have hinj : Function.Injective f := fun i j he =>
    plane_index_injective P ((hf i).trans ((congrArg Q.plane he).trans (hf j).symm))
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := plane_cover_from_unit_levels Q P (fun x hx => (levels x hx).symm) j
    exact ⟨i, plane_index_injective Q ((hf i).symm.trans hi.symm)⟩
  let e : ι ≃ κ := Equiv.ofBijective f ⟨hinj, hsurj⟩
  let R := reindexPlaneSystem Q e
  have hr : R = P := planeSystem_eq_of_pointwise fun i => (hf i).symm
  have hc : IsClosedPlaneSystem g R := fun i => cg (e i)
  have hp : interactionCubic (planePencil g R) s = interactionCubic (planePencil g Q) s :=
    interactionCubic_pencil_reindex Q e g s
  have he : EqualPlaneTripleEnergies h g P c t s := by
    intro i j k _ _ _ x _
    have hh : normalizedPencilEnergy g P c s x = normalizedPencilEnergy g Q c s x := by
      rw [← hr]
      unfold normalizedPencilEnergy
      rw [hp]
    exact (eq x).trans hh.symm
  rw [hr] at hc hp
  obtain ⟨hts, hh⟩ := planePencil_labeled_recovery rh rg ch hc m he
  refine ⟨e, hf, hts, ?_⟩
  simpa only [hp] using hh ht.ne' ht₁

end
end ThirteenPlanes.RoundCubics
