module

public import ThirteenPlanes.Peirce.Slots
public import ThirteenPlanes.PlanePencilSplit
public import ThirteenPlanes.OrthogonalIsotope

@[expose] public section

set_option backward.privateInPublic true

/-! The four candidate plane counts before the seven-plane exclusion. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] {planes : PlaneDecomposition V ι}
variable {h : SymmetricCubic V} {c : ℝ}

omit [Fintype ι] in
/-- A closed plane supplies the actual unit idempotent and a unit minus field. -/
theorem markedPair_of_closed_plane (round : IsRound h 1) (closed : IsClosedPlaneSystem h planes)
    (i : ι) :
    ∃ (a : V) (b : minusSpace h a),
      a ∈ planes.plane i ∧ (b : V) ∈ planes.plane i ∧ IsUnitIdempotent h a ∧ ‖b‖ = 1 := by
  obtain ⟨⟨z, hz⟩, _, _⟩ := RoundCubics.planeSquareModel round closed i
  let a : planes.plane i := z.symm 1
  let b : planes.plane i := z.symm Complex.I
  have hza : z a = 1 := z.apply_symm_apply 1
  have hzb : z b = Complex.I := z.apply_symm_apply Complex.I
  have square_of_coordinate (x y : planes.plane i) (hy : z y = (star (z x)) ^ 2) :
      h.L (x : V) (x : V) = (y : V) := by
    have he : (⟨h.L x x, closed i x.property x.property⟩ : planes.plane i) = y := by
      apply z.injective
      rw [hz, Real.sqrt_one, one_smul, hy]
    exact congrArg Subtype.val he
  have ha_sq : h.L (a : V) (a : V) = (a : V) := by
    apply square_of_coordinate
    simp [hza]
  have hb_sq : h.L (b : V) (b : V) = -(a : V) := by
    change h.L (b : V) (b : V) = ((-a : planes.plane i) : V)
    apply square_of_coordinate
    simp [hza, hzb, Complex.I_sq]
  have hab_sq : h.L ((a : V) + (b : V)) ((a : V) + (b : V)) = (-2 : ℝ) • (b : V) := by
    change h.L ((a + b : planes.plane i) : V) ((a + b : planes.plane i) : V) =
      ((-2 : ℝ) • b : planes.plane i)
    apply square_of_coordinate
    rw [map_smul, map_add, hza, hzb, star_add, star_one]
    apply Complex.ext <;>
      norm_num [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.real_smul]
  have hab : h.L (a : V) (b : V) = -(b : V) := by
    simp only [map_add, LinearMap.add_apply, ha_sq, hb_sq, h.L_comm (b : V) (a : V)] at hab_sq
    have he := congrArg ((1 / 2 : ℝ) • ·) hab_sq
    convert he using 1 <;> module
  have ha_norm : ‖(a : V)‖ = 1 := by simpa [hza] using (z.norm_map a).symm
  have hb_norm : ‖(b : V)‖ = 1 := by simpa [hzb] using (z.norm_map b).symm
  have hb_minus : (b : V) ∈ minusSpace h (a : V) := mem_eigenspace_iff.mpr (by simpa using hab)
  exact ⟨(a : V), ⟨(b : V), hb_minus⟩, a.property, b.property, ⟨ha_norm, ha_sq⟩, hb_norm⟩

omit [Fintype ι] [FiniteDimensional ℝ V] in
private theorem normalize_closed_system (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) :
    ∃ g : SymmetricCubic V, IsRound g 1 ∧ IsClosedPlaneSystem g planes := by
  let r := (Real.sqrt c)⁻¹
  let g := r • h
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr round.positive
  have hr : r ^ 2 * c = 1 := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt round.positive.le, inv_mul_cancel₀ round.positive.ne']
  have gr : IsRound g 1 := by
    refine ⟨by norm_num, fun x => ?_⟩
    change ‖(r • h).squareMap x‖ ^ 2 = _
    rw [SymmetricCubic.squareMap_smul, norm_smul, mul_pow, Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
      round.square_norm, ← mul_assoc, hr, one_mul]
  have gc : IsClosedPlaneSystem g planes := by
    intro i x y hx hy
    change (r • h).L x y ∈ planes.plane i
    simpa only [map_smul, LinearMap.smul_apply] using (planes.plane i).smul_mem r (closed i hx hy)
  exact ⟨g, gr, gc⟩

private theorem orthogonal_product_dimension_cases {S₁ S₂ S₃ : Type*}
    [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁]
    [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂]
    [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃]
    [FiniteDimensional ℝ S₁] [FiniteDimensional ℝ S₂] [FiniteDimensional ℝ S₃]
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (hφ : ∀ u y, ‖φ u y‖ = ‖u‖ * ‖y‖)
    {k : ℕ} (hk : 0 < k) (h₁ : Module.finrank ℝ S₁ = k) (h₂ : Module.finrank ℝ S₂ = k)
    (h₃ : Module.finrank ℝ S₃ = k) : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 :=
  (MarkedPlane.orthogonalProduct_isotopicToHurwitz φ hφ hk h₁ h₂ h₃).1

private theorem hurwitz_slot_counts {g : SymmetricCubic V} {a : V} {b : minusSpace g a}
    (gr : IsRound g 1) (ha : IsUnitIdempotent g a) (hb : ‖b‖ = 1)
    (ht : LinearMap.trace ℝ V (g.L a) = 0) (hk : 0 < (Module.finrank ℝ V - 2) / 3) :
    let k := (Module.finrank ℝ V - 2) / 3
    k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 := by
  obtain ⟨h₁, h₂, h₃⟩ := slot_finranks gr ha hb ht hk
  let φ : slotOne b →ₗ[ℝ] slotTwo gr ha b →ₗ[ℝ] slotThree gr ha b :=
    slotProduct gr ha (b := b)
  have hφ (u : slotOne b) (y : slotTwo gr ha b) : ‖φ u y‖ = ‖u‖ * ‖y‖ :=
    slotProduct_norm gr ha u y
  let : FiniteDimensional ℝ ↥(slotOne b) :=
    FiniteDimensional.of_injective (slotOne b).subtype (slotOne b).subtype_injective
  let : FiniteDimensional ℝ ↥(halfSpace g a) :=
    FiniteDimensional.of_injective (halfSpace g a).subtype (halfSpace g a).subtype_injective
  let : FiniteDimensional ℝ ↥(slotTwo gr ha b) :=
    FiniteDimensional.of_injective (slotTwo gr ha b).subtype (slotTwo gr ha b).subtype_injective
  let : FiniteDimensional ℝ ↥(slotThree gr ha b) :=
    FiniteDimensional.of_injective (slotThree gr ha b).subtype (slotThree gr ha b).subtype_injective
  exact orthogonal_product_dimension_cases
    (S₁ := ↥(slotOne b)) (S₂ := ↥(slotTwo gr ha b)) (S₃ := ↥(slotThree gr ha b))
    (k := (Module.finrank ℝ V - 2) / 3) φ hφ hk h₁ h₂ h₃

private theorem plane_count_from_slot_count {m k : ℕ}
    (hm : m % 3 = 1) (hk : k = 2 * (m - 1) / 3) (hproper : 1 < m)
    (hc : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8) : m = 4 ∨ m = 7 ∨ m = 13 := by
  rcases hc with he | he | he | he <;> omega

/-- Corollary 2b-four-seven, at arbitrary positive original round strength. -/
theorem planeCount_one_four_seven_thirteen (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (hm : 1 ≤ Fintype.card ι) :
    Fintype.card ι = 1 ∨ Fintype.card ι = 4 ∨ Fintype.card ι = 7 ∨ Fintype.card ι = 13 := by
  by_cases hm₁ : Fintype.card ι = 1
  · exact Or.inl hm₁
  have hproper : 1 < Fintype.card ι := lt_of_le_of_ne hm (Ne.symm hm₁)
  obtain ⟨g, gr, gc⟩ := normalize_closed_system round closed
  have hnonempty : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_one.trans hproper)
  obtain ⟨i⟩ := hnonempty
  obtain ⟨a, b, hai, _, ha, hb⟩ := markedPair_of_closed_plane gr gc i
  have ht : LinearMap.trace ℝ V (g.L a) = 0 :=
    RoundCubics.traceFree_of_isClosedPlaneSystem gr gc a
  have hmk := slot_dimension_of_closed_planes gr ha gc i hai hproper
  have hk : 0 < (Module.finrank ℝ V - 2) / 3 := (by decide : 0 < 2).trans_le hmk.2
  have hclass := hurwitz_slot_counts gr ha hb ht hk
  obtain ⟨_, hmod, _, _, _, _⟩ := closedPlaneDimensions gr gc ha i hai
  exact Or.inr (plane_count_from_slot_count hmod hmk.1 hproper hclass)


/-- The four matrix planes realize the slot hypotheses with all three slot dimensions equal to two. -/
theorem fourPlane_slotWitness :
    ∃ (g : SymmetricCubic TracelessHermitian3) (gr : IsRound g 1)
        (a : TracelessHermitian3) (ha : IsUnitIdempotent g a) (b : minusSpace g a),
      ‖b‖ = 1 ∧
      IsClosedPlaneSystem g fourPlaneDecomposition ∧
      a ∈ fourPlaneDecomposition.plane 0 ∧ (b : TracelessHermitian3) ∈ fourPlaneDecomposition.plane 0 ∧
      LinearMap.trace ℝ TracelessHermitian3 (g.L a) = 0 ∧
      Module.finrank ℝ (slotOne b) = 2 ∧
      Module.finrank ℝ (slotTwo gr ha b) = 2 ∧
      Module.finrank ℝ (slotThree gr ha b) = 2 := by
  obtain ⟨g, gr, gt, gc⟩ := PencilEnergy.fourPlane_roundWitness 1 (by norm_num)
  obtain ⟨a, b, hai, hbi, ha, hb⟩ := markedPair_of_closed_plane gr gc 0
  have hd : Module.finrank ℝ TracelessHermitian3 = 8 := by
    simpa using finrank_eq_twice_card fourPlaneDecomposition
  have hk : 0 < (Module.finrank ℝ TracelessHermitian3 - 2) / 3 := by norm_num [hd]
  obtain ⟨h₁, h₂, h₃⟩ := slot_finranks gr ha hb (gt a) hk
  norm_num [hd] at h₁ h₂ h₃
  exact ⟨g, gr, a, ha, b, hb, gc, hai, hbi, gt a, h₁, h₂, h₃⟩

end

end ThirteenPlanes.Peirce
