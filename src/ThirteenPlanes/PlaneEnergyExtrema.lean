module

public import ThirteenPlanes.PlanePencilEnergy

@[expose] public section

set_option backward.privateInPublic true

/-! The distance bound and the exact extremal sets of the directional energy. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

open SymmetricCubic PlaneContractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {c : ℝ}
  {ι : Type*} [Fintype ι] {planes : PlaneDecomposition V ι}

omit [Fintype ι] in
private theorem projection_deficit (x : V) (hx : ‖x‖ = 1) (i : ι) :
    ‖x - planes.proj i x‖ ^ 2 = 1 - ‖planes.proj i x‖ ^ 2 := by
  have hm : planes.proj i x ∈ planes.plane i := (piP planes i x).property
  have ho : ⟪planes.proj i x, x - planes.proj i x⟫ = 0 :=
    (Submodule.mem_orthogonal (planes.plane i) _).mp (sub_mem_orthogonal planes i x) _ hm
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (planes.proj i x) (x - planes.proj i x) ho
  rw [show planes.proj i x + (x - planes.proj i x) = x by abel, hx] at hs
  nlinarith only [hs]

private theorem projected_squares_sum (x : V) (hx : ‖x‖ = 1) :
    ∑ i, ‖planes.proj i x‖ ^ 2 = 1 := by
  have hsum := sum_inner_piP planes x x
  simp only [real_inner_self_eq_norm_sq, hx, one_pow] at hsum
  exact hsum

private theorem planeUnion_distance [Nonempty ι] (x : V) (hx : ‖x‖ = 1) :
    let U : Set V := ⋃ i, (planes.plane i : Set V)
    (∃ i, Metric.infDist x U = ‖x - planes.proj i x‖) ∧
      Metric.infDist x U ^ 2 ≤ 1 - ∑ i, ‖planes.proj i x‖ ^ 4 := by
  classical
  let U : Set V := ⋃ i, (planes.plane i : Set V)
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : ι => ‖planes.proj i x‖ ^ 2) Finset.univ_nonempty
  have hproj : planes.proj i x ∈ U :=
    Set.mem_iUnion.mpr ⟨i, (piP planes i x).property⟩
  have hd : Metric.infDist x U = ‖x - planes.proj i x‖ := by
    apply le_antisymm
    · simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := x) hproj
    · apply (Metric.le_infDist ⟨_, hproj⟩).2
      intro y hy
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
      calc
        _ ≤ ‖x - planes.proj j x‖ := by
          apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
            (by decide : (2 : ℕ) ≠ 0)).mp
          rw [projection_deficit x hx, projection_deficit x hx]
          exact sub_le_sub_left (hmax j (Finset.mem_univ j)) 1
        _ = Metric.infDist x (planes.plane j) := by
          rw [← dist_eq_norm]
          exact (planes.plane j).dist_starProjection_eq_infDist x
        _ ≤ _ := Metric.infDist_le_dist_of_mem hyj
  have hsum : (∑ j, ‖planes.proj j x‖ ^ 4) ≤ ‖planes.proj i x‖ ^ 2 := by
    calc
      _ = ∑ j, ‖planes.proj j x‖ ^ 2 * ‖planes.proj j x‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j, ‖planes.proj i x‖ ^ 2 * ‖planes.proj j x‖ ^ 2 :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hmax j hj) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum, projected_squares_sum x hx, mul_one]
  refine ⟨⟨i, hd⟩, ?_⟩
  rw [hd, projection_deficit x hx]
  exact sub_le_sub_left hsum 1

private theorem energy_eq_one_on_plane (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) (t : ℝ) (x : V) (hx : ‖x‖ = 1) (i : ι)
    (hxi : x ∈ planes.plane i) : normalizedPencilEnergy h planes c t x = 1 := by
  let u : planes.plane i := ⟨x, hxi⟩
  have hm : (planePencil h planes).mixingCubic.squareMap x = 0 := by
    apply ext_inner_right ℝ
    intro y
    rw [inner_zero_left]
    exact planePencil_mixing_repeated closed i u u y
  have he : (interactionCubic (planePencil h planes) t).squareMap x = h.squareMap x := by
    have hone := congrArg (fun g : SymmetricCubic V => g.squareMap x) (planePencil_at_one h planes)
    simp only [interactionCubic, coupling_apply, one_smul, squareMap_add, squareMap_smul,
      hm, smul_zero, add_zero] at hone ⊢
    exact hone
  rw [normalizedPencilEnergy, he, round.square_norm, hx, one_pow, mul_one, div_self round.positive.ne']

/-- The energy extrema, with the metric distance to the actual union of subspaces. -/
theorem planePencilExtrema (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (hm : 1 < Fintype.card ι) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≠ 1) :
    let f := normalizedPencilEnergy h planes c t
    let S : Set V := {x | ‖x‖ = 1}
    let U : Set V := ⋃ i, (planes.plane i : Set V)
    (∀ x ∈ S, Metric.infDist x U ^ 2 ≤ |f x - 1| / |t - 1| ∧ (f x = 1 ↔ x ∈ U)) ∧
    (t < 1 → IsGreatest (f '' S) 1 ∧ {x | x ∈ S ∧ IsMaxOn f S x} = S ∩ U) ∧
    (1 < t → IsLeast (f '' S) 1 ∧ {x | x ∈ S ∧ IsMinOn f S x} = S ∩ U) := by
  let : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hm
  let f := normalizedPencilEnergy h planes c t
  let S : Set V := {x | ‖x‖ = 1}
  let U : Set V := ⋃ i, (planes.plane i : Set V)
  let B (x : V) := 1 - (∑ i, ‖planes.proj i x‖ ^ 4) +
    t / c * ‖(planePencil h planes).mixingCubic.squareMap x‖ ^ 2
  have hdir (x : V) (hx : x ∈ S) : f x - 1 = (t - 1) * B x :=
    planePencil_directional_energy round closed t x hx
  have hpoint (x : V) (hx : x ∈ S) :
      0 ≤ B x ∧ Metric.infDist x U ^ 2 ≤ |f x - 1| / |t - 1| ∧ (f x = 1 ↔ x ∈ U) := by
    obtain ⟨⟨i, hi⟩, hd⟩ := planeUnion_distance (planes := planes) x hx
    have hpositive : 0 ≤ t / c * ‖(planePencil h planes).mixingCubic.squareMap x‖ ^ 2 :=
      mul_nonneg (div_nonneg ht₀ round.positive.le) (sq_nonneg _)
    have hb : Metric.infDist x U ^ 2 ≤ B x := le_trans hd (le_add_of_nonneg_right hpositive)
    have hb₀ := (sq_nonneg (Metric.infDist x U)).trans hb
    have habs : |f x - 1| / |t - 1| = B x := by
      rw [hdir x hx, abs_mul, abs_of_nonneg hb₀, mul_comm,
        mul_div_cancel_right₀ _ (abs_ne_zero.mpr (sub_ne_zero.mpr ht₁))]
    refine ⟨hb₀, habs ▸ hb, ?_, ?_⟩
    · intro h
      have hB : B x = 0 := by
        rw [← habs, h, sub_self, abs_zero, zero_div]
      have hz : Metric.infDist x U ^ 2 = 0 :=
        le_antisymm (hB ▸ hb) (sq_nonneg _)
      rw [hi, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), norm_eq_zero, sub_eq_zero] at hz
      exact Set.mem_iUnion.mpr ⟨i, hz.symm ▸ (piP planes i x).property⟩
    · intro h
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp h
      exact energy_eq_one_on_plane round closed t x hx i hxi
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let e := (stdOrthonormalBasis ℝ (planes.plane i₀)).reindex (finCongr (planes.dimension i₀))
  let x₀ : V := (e 0 : planes.plane i₀)
  have hx₀ : x₀ ∈ S := e.orthonormal.1 0
  have hu₀ : x₀ ∈ U := Set.mem_iUnion.mpr ⟨i₀, (e 0).property⟩
  have he₀ : f x₀ = 1 := (hpoint x₀ hx₀).2.2.mpr hu₀
  have hin : (1 : ℝ) ∈ f '' S := ⟨x₀, hx₀, he₀⟩
  refine ⟨fun x hx => (hpoint x hx).2, ?_, ?_⟩
  · intro ht
    have hle (x : V) (hx : x ∈ S) : f x ≤ 1 := by
      exact sub_nonpos.mp (hdir x hx ▸
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.le) (hpoint x hx).1)
    refine ⟨⟨hin, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hle x hx
    · ext x
      change (x ∈ S ∧ IsMaxOn f S x) ↔ x ∈ S ∧ x ∈ U
      rw [isMaxOn_iff]
      constructor
      · rintro ⟨hx, hmax⟩
        exact ⟨hx, (hpoint x hx).2.2.mp
          (le_antisymm (hle x hx) (he₀ ▸ hmax x₀ hx₀))⟩
      · rintro ⟨hx, hu⟩
        exact ⟨hx, fun y hy => ((hpoint x hx).2.2.mpr hu).symm ▸ hle y hy⟩
  · intro ht
    have hle (x : V) (hx : x ∈ S) : 1 ≤ f x := by
      exact sub_nonneg.mp (hdir x hx ▸
        mul_nonneg (sub_nonneg.mpr ht.le) (hpoint x hx).1)
    refine ⟨⟨hin, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hle x hx
    · ext x
      change (x ∈ S ∧ IsMinOn f S x) ↔ x ∈ S ∧ x ∈ U
      rw [isMinOn_iff]
      constructor
      · rintro ⟨hx, hmin⟩
        exact ⟨hx, (hpoint x hx).2.2.mp
          (le_antisymm (he₀ ▸ hmin x₀ hx₀) (hle x hx))⟩
      · rintro ⟨hx, hu⟩
        exact ⟨hx, fun y hy => ((hpoint x hx).2.2.mpr hu).symm ▸ hle y hy⟩

end ThirteenPlanes.RoundCubics
