module

public import ThirteenPlanes.MatrixLinePlanes
public import ThirteenPlanes.SignedEnergyBasic

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

private theorem matrixLineEmbed_inner (x y : TracelessHermitian3) :
    inner ℝ (matrixLineEmbed x) (matrixLineEmbed y) = inner ℝ x y := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (matrixLineEmbed x),
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x,
    ← matrixLineEmbed.map_add]
  simp only [matrixLineEmbed.norm_map]

theorem matrixLineEmbed_planeProjection (k : Fin 4) (x : TracelessHermitian3) :
    (signedPlane (matrixLineGrade k)).starProjection (matrixLineEmbed x) =
      matrixLineEmbed (matrixFrameProjection k x) := by
  have hp := matrixLineEmbed_matrixPlane k
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← hp]
    exact ⟨matrixFrameProjection k x, ⟨x, rfl⟩, rfl⟩
  · intro y hy
    rw [← hp] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [← matrixLineEmbed.map_sub]
    change inner ℝ (matrixLineEmbed (x - matrixFrameProjection k x)) (matrixLineEmbed z) = 0
    rw [matrixLineEmbed_inner, inner_sub_left,
      matrixFrameProjection_inner_swap, (mem_matrixPlane_iff k z).mp hz, sub_self]

private theorem signedDiagonalCubic_sum_square (x : SignedField) :
    signedDiagonalCubic.squareMap x =
      ∑ p, signedEqualCubic.squareMap ((signedPlane p).starProjection x) := by
  rw [SymmetricCubic.squareMap, signedDiagonalCubic_L_coords]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [signedPlane_starProjection_apply, SymmetricCubic.squareMap, signedEqualCubic_L_same_plane]

theorem matrixLineEmbed_diagonalSquare (x : TracelessHermitian3) :
    signedDiagonalCubic.squareMap (matrixLineEmbed x) =
      matrixLineEmbed (matrixDiagonalCubic.squareMap x) := by
  rw [signedDiagonalCubic_sum_square, matrixDiagonalCubic_squareMap, map_sum]
  classical
  let f : SignedPlaneIndex → SignedField :=
    fun p => signedEqualCubic.squareMap ((signedPlane p).starProjection (matrixLineEmbed x))
  change (∑ p, f p) = _
  calc
    (∑ p, f p) = ∑ p ∈ Finset.univ.image matrixLineGrade, f p := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ hp
      have h₃ : p.val.val 2 ≠ 0 := by
        intro hz
        obtain ⟨k, rfl⟩ := matrixLineGrade_covers p hz
        exact hp (Finset.mem_image_of_mem _ (Finset.mem_univ k))
      have hc : signedPlaneCoordinates (matrixLineEmbed x) p = 0 := by
        rw [signedPlaneCoordinates_apply]
        exact matrixLineEmbed_off_charge x p.val h₃
      change signedEqualCubic.squareMap ((signedPlane p).starProjection (matrixLineEmbed x)) = 0
      rw [signedPlane_starProjection_apply, hc, map_zero]
      simp [SymmetricCubic.squareMap]
    _ = ∑ k : Fin 4, f (matrixLineGrade k) := by
      rw [Finset.sum_image (fun _ _ _ _ h => matrixLineGrade_injective h)]
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [f, matrixLineEmbed_planeProjection, matrixLineEmbed_equalSquare,
        matrixEqualCubic_squareMap]

private theorem coupling_signedPair_sub (a b : ℝ) :
    coupling signedPair (a,b) = (a-b) • signedDiagonalCubic + b • signedEqualCubic := by
  apply SymmetricCubic.ext
  intro x y z
  have hs : (signedEqualCubic - signedDiagonalCubic).apply x y z =
      signedEqualCubic.apply x y z - signedDiagonalCubic.apply x y z := by
    simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]
  simp only [coupling_apply, signedPair, SymmetricCubic.apply_add, SymmetricCubic.apply_smul, hs]
  ring

/-- The whole ambient square intertwines the representative matrix line at every coupling. -/
theorem matrixLineEmbed_coupling_square (u : ℝ × ℝ) (x : TracelessHermitian3) :
    (coupling signedPair u).squareMap (matrixLineEmbed x) =
      matrixLineEmbed ((coupling fourPlanePair u).squareMap x) := by
  obtain ⟨a,b⟩ := u
  rw [coupling_signedPair_sub, coupling_fourPlanePair]
  simp only [SymmetricCubic.squareMap_add, SymmetricCubic.squareMap_smul, map_add, map_smul,
    matrixLineEmbed_diagonalSquare, matrixLineEmbed_equalSquare]

/-- Unit-normalized energy agrees with the pilot on every field of the representative line. -/
theorem matrixLineEmbed_coupling_energy (u : ℝ × ℝ) (x : TracelessHermitian3) :
    unitEnergy (coupling signedPair u) (matrixLineEmbed x) = unitEnergy (coupling fourPlanePair u) x := by
  rw [unitEnergy, unitEnergy, matrixLineEmbed_coupling_square, matrixLineEmbed.norm_map]

/-- The representative matrix line is exactly the support on third charge zero. -/
theorem mem_matrixLineEmbed_range_iff (x : SignedField) :
    x ∈ LinearMap.range matrixLineEmbed.toLinearMap ↔
      ∀ q : NonzeroCharge, q.val 2 ≠ 0 → signedCoordinates x q = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ q hq
    exact matrixLineEmbed_off_charge y q hq
  · intro hx
    rw [← signedPlane_sum x]
    apply Submodule.sum_mem
    intro p _
    by_cases hp : p.val.val 2 = 0
    · obtain ⟨k, rfl⟩ := matrixLineGrade_covers p hp
      have hmem : signedPlaneInclusion (matrixLineGrade k)
          (signedPlaneCoordinates x (matrixLineGrade k)) ∈ signedPlane (matrixLineGrade k) :=
        ⟨_, rfl⟩
      rw [← matrixLineEmbed_matrixPlane] at hmem
      obtain ⟨v, _, hv⟩ := hmem
      exact ⟨v, hv⟩
    · have hc : signedPlaneCoordinates x p = 0 := hx p.val hp
      rw [hc, map_zero]
      exact (LinearMap.range matrixLineEmbed.toLinearMap).zero_mem

end

end ThirteenPlanes
